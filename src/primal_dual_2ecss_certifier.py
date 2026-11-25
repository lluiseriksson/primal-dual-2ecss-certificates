"""Pure-stdlib zero-float verifier for PRIMAL-DUAL-2ECSS-CERT-1.0 certificates.
Supports four exact-Q verification modes aligned with Danciu & Ibrahimpur (arXiv:2611.32924, Nov 25, 2026)
"Better-than-3 Approximation for 2ECSS Using the Primal-Dual Method":
  1. primal_dual_2ecss_solution_exact      (Thm 1.1 & Lemma 3.1: 2ECSS feasibility/minimality, cut-LP dual & <3 ratio)
  2. thm12_minimal_augmentation_exact      (Thm 1.2: exact weighted augmentation-incidence bound on forest H + A)
  3. nonuniform_beta_ratio_optimality_exact (Lemma 3.4 & Thm 3.5: exact rational beta, alpha(beta) < 3, sqrt(3)+1 bound)
  4. primal_dual_trace_telescoping_exact   (Lemmas 3.1-3.4: potential 2n -> 2, per-step ratio & telescoped sum)

Author: Lluis Eriksson
"""
from __future__ import annotations

import re
from fractions import Fraction
from typing import Any, Dict, List, Tuple

from src.primal_dual_2ecss_exact import (
    approx_ratio_exact,
    is_2_edge_connected,
    is_forest_and_decompose,
)

SCHEMA_VERSION = "PRIMAL-DUAL-2ECSS-CERT-1.0"
_CANON_INT_RE = re.compile(r"\A(?:0|-?[1-9][0-9]*)\Z")
_CANON_FRAC_RE = re.compile(r"\A-?[1-9][0-9]*/[1-9][0-9]*\Z")


class PrimalDual2ECSSCertificateError(ValueError):
    """Raised whenever any PRIMAL-DUAL-2ECSS-CERT-1.0 verification check fails."""


def _assert_strict_json_types(obj: Any, path: str = "root") -> None:
    t = type(obj)
    if t is int or t is str or obj is None:
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise PrimalDual2ECSSCertificateError(f"Non-str dict key at {path}: {type(k).__name__}")
            _assert_strict_json_types(v, f"{path}.{k}")
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]")
        return
    raise PrimalDual2ECSSCertificateError(f"Forbidden type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise PrimalDual2ECSSCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is int:
        return Fraction(val, 1)
    if type(val) is str:
        if _CANON_INT_RE.match(val):
            return Fraction(int(val), 1)
        if _CANON_FRAC_RE.match(val):
            num_s, den_s = val.split("/")
            num, den = int(num_s), int(den_s)
            if den < 2:
                raise PrimalDual2ECSSCertificateError(f"{name} denominator must be >= 2: {val!r}")
            q = Fraction(num, den)
            if q.numerator != num or q.denominator != den:
                raise PrimalDual2ECSSCertificateError(f"{name} unreduced fraction: {val!r}")
            return q
        raise PrimalDual2ECSSCertificateError(f"{name} non-canonical rational string: {val!r}")
    raise PrimalDual2ECSSCertificateError(f"{name} invalid type {type(val).__name__}")


def _verify_mode1_solution(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "n_vertices", "edges", "beta",
        "solution_edge_indices", "dual_cuts", "dual_z",
        "claimed_primal_cost", "claimed_dual_obj", "claimed_alpha_bound",
    }
    if set(cert.keys()) != req:
        raise PrimalDual2ECSSCertificateError(f"Mode 1 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["n_vertices"], "n_vertices")
    if not (3 <= n <= 32):
        raise PrimalDual2ECSSCertificateError(f"n_vertices must be in [3, 32], got {n}")
    beta = _parse_rat(cert["beta"], "beta")
    if not (Fraction(0, 1) <= beta <= Fraction(1, 2)):
        raise PrimalDual2ECSSCertificateError(f"beta must lie in [0, 1/2], got {beta}")

    e_raw = cert["edges"]
    if type(e_raw) is not list or len(e_raw) < n or len(e_raw) > 256:
        raise PrimalDual2ECSSCertificateError("edges length invalid")
    edges: List[Tuple[int, int, Fraction]] = []
    for idx, er in enumerate(e_raw):
        if type(er) is not list or len(er) != 3:
            raise PrimalDual2ECSSCertificateError(f"edges[{idx}] must be [u, v, cost]")
        u, v = _parse_int(er[0], f"edges[{idx}].u"), _parse_int(er[1], f"edges[{idx}].v")
        c = _parse_rat(er[2], f"edges[{idx}].cost")
        if not (0 <= u < n and 0 <= v < n) or u == v or c < 0:
            raise PrimalDual2ECSSCertificateError(f"Invalid multigraph edge or negative cost at {idx}")
        edges.append((u, v, c))

    sol_raw = cert["solution_edge_indices"]
    if type(sol_raw) is not list or not sol_raw:
        raise PrimalDual2ECSSCertificateError("solution_edge_indices must be non-empty list")
    sol_idx = [_parse_int(x, f"sol[{i}]") for i, x in enumerate(sol_raw)]
    if len(set(sol_idx)) != len(sol_idx) or any(not (0 <= x < len(edges)) for x in sol_idx):
        raise PrimalDual2ECSSCertificateError("solution_edge_indices must be distinct valid edge indices")

    sol_uv = [(edges[i][0], edges[i][1]) for i in sol_idx]
    if not is_2_edge_connected(n, sol_uv):
        raise PrimalDual2ECSSCertificateError("Solution subgraph (V, F) is NOT 2-edge-connected")
    # Verify inclusion-minimality (reverse-delete guarantee)
    for k in range(len(sol_uv)):
        if is_2_edge_connected(n, [sol_uv[j] for j in range(len(sol_uv)) if j != k]):
            raise PrimalDual2ECSSCertificateError(f"Solution is not minimal: edge index {sol_idx[k]} is redundant")

    # Parse and verify dual cuts y_S > 0 and z_e >= 0
    dc_raw = cert["dual_cuts"]
    dz_raw = cert["dual_z"]
    if type(dc_raw) is not list or type(dz_raw) is not list or len(dz_raw) != len(edges):
        raise PrimalDual2ECSSCertificateError("dual_cuts or dual_z invalid shape")
    z_duals = [_parse_rat(x, f"dual_z[{i}]") for i, x in enumerate(dz_raw)]
    if any(z < 0 for z in z_duals):
        raise PrimalDual2ECSSCertificateError("dual_z must be nonnegative")

    y_sum = Fraction(0, 1)
    loads = [Fraction(0, 1)] * len(edges)
    seen_cuts = set()
    for idx, item in enumerate(dc_raw):
        if type(item) is not list or len(item) != 2:
            raise PrimalDual2ECSSCertificateError(f"dual_cuts[{idx}] must be [S_vertices, y_S]")
        s_raw, y_raw = item
        if type(s_raw) is not list or not (1 <= len(s_raw) <= n - 1):
            raise PrimalDual2ECSSCertificateError(f"dual_cuts[{idx}] S must be proper non-empty subset")
        s_verts = [_parse_int(v, f"cut[{idx}]") for v in s_raw]
        if len(set(s_verts)) != len(s_verts) or any(not (0 <= v < n) for v in s_verts):
            raise PrimalDual2ECSSCertificateError(f"dual_cuts[{idx}] invalid vertex set")
        Skey = tuple(sorted(s_verts))
        if Skey in seen_cuts:
            raise PrimalDual2ECSSCertificateError(f"Duplicate dual cut {Skey}")
        seen_cuts.add(Skey)
        yv = _parse_rat(y_raw, f"dual_cuts[{idx}].y")
        if yv <= 0:
            raise PrimalDual2ECSSCertificateError(f"dual_cuts[{idx}] y_S must be > 0")
        y_sum += yv
        Sset = set(Skey)
        for eid, (u, v, _) in enumerate(edges):
            if (u in Sset) != (v in Sset):
                loads[eid] += yv

    for eid, (_, _, cost) in enumerate(edges):
        if loads[eid] - z_duals[eid] > cost:
            raise PrimalDual2ECSSCertificateError(f"Dual constraint 3b violated on edge {eid}: {loads[eid] - z_duals[eid]} > {cost}")

    primal_cost = sum((edges[i][2] for i in sol_idx), Fraction(0, 1))
    dual_obj = 2 * y_sum - sum(z_duals, Fraction(0, 1))
    if dual_obj > primal_cost:
        raise PrimalDual2ECSSCertificateError("Impossible: weak duality dual_obj <= primal_cost violated")
    _, _, alpha = approx_ratio_exact(beta)
    if primal_cost > alpha * dual_obj:
        raise PrimalDual2ECSSCertificateError(f"Approximation bound violated: {primal_cost} > {alpha} * {dual_obj}")

    if _parse_rat(cert["claimed_primal_cost"], "claimed_primal_cost") != primal_cost:
        raise PrimalDual2ECSSCertificateError("claimed_primal_cost mismatch")
    if _parse_rat(cert["claimed_dual_obj"], "claimed_dual_obj") != dual_obj:
        raise PrimalDual2ECSSCertificateError("claimed_dual_obj mismatch")
    if _parse_rat(cert["claimed_alpha_bound"], "claimed_alpha_bound") != alpha:
        raise PrimalDual2ECSSCertificateError("claimed_alpha_bound mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n_vertices": n,
        "beta": str(beta),
        "alpha_bound": str(alpha),
        "primal_cost": str(primal_cost),
        "dual_obj": str(dual_obj),
    }


def _verify_mode2_thm12_aug(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "n_vertices", "forest_edges", "augmentation_edges",
        "beta", "claimed_lhs", "claimed_rhs",
    }
    if set(cert.keys()) != req:
        raise PrimalDual2ECSSCertificateError(f"Mode 2 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["n_vertices"], "n_vertices")
    if not (3 <= n <= 32):
        raise PrimalDual2ECSSCertificateError(f"n_vertices must be in [3, 32], got {n}")
    beta = _parse_rat(cert["beta"], "beta")
    if not (Fraction(0, 1) <= beta <= Fraction(1, 2)):
        raise PrimalDual2ECSSCertificateError("beta must lie in [0, 1/2]")

    def parse_pairs(raw: Any, label: str) -> List[Tuple[int, int]]:
        if type(raw) is not list:
            raise PrimalDual2ECSSCertificateError(f"{label} must be list")
        out = []
        for idx, e in enumerate(raw):
            if type(e) is not list or len(e) != 2:
                raise PrimalDual2ECSSCertificateError(f"{label}[{idx}] must be [u, v]")
            u, v = _parse_int(e[0], f"{label}[{idx}].u"), _parse_int(e[1], f"{label}[{idx}].v")
            if not (0 <= u < n and 0 <= v < n) or u == v:
                raise PrimalDual2ECSSCertificateError(f"{label}[{idx}] invalid endpoints")
            out.append((u, v))
        return out

    f_edges = parse_pairs(cert["forest_edges"], "forest_edges")
    a_edges = parse_pairs(cert["augmentation_edges"], "augmentation_edges")
    if not a_edges:
        raise PrimalDual2ECSSCertificateError("augmentation_edges must be non-empty")

    ok, leaves, isolated, nontrivial = is_forest_and_decompose(n, f_edges)
    if not ok:
        raise PrimalDual2ECSSCertificateError("forest_edges contains a cycle (not a forest)")
    if len(leaves) < 2 * len(nontrivial):
        raise PrimalDual2ECSSCertificateError("Impossible: |L| < 2|C| on forest")

    combined = f_edges + a_edges
    if not is_2_edge_connected(n, combined):
        raise PrimalDual2ECSSCertificateError("(V, F u A) is NOT 2-edge-connected")
    for k in range(len(a_edges)):
        sub = f_edges + [a_edges[j] for j in range(len(a_edges)) if j != k]
        if is_2_edge_connected(n, sub):
            raise PrimalDual2ECSSCertificateError(f"Augmentation A is not minimal: A[{k}] is redundant")

    # Compute exact Theorem 1.2 LHS and RHS over Q
    leaf_iso_set = set(leaves) | set(isolated)
    lhs_li = sum((1 if u in leaf_iso_set else 0) + (1 if v in leaf_iso_set else 0) for (u, v) in a_edges)
    lhs_c = 0
    for comp in nontrivial:
        cset = set(comp)
        lhs_c += sum(1 for (u, v) in a_edges if (u in cset) != (v in cset))
    lhs = Fraction(lhs_li, 1) + beta * lhs_c
    rhs = 2 * (Fraction(1, 1) + beta) * (len(leaves) + 2 * len(isolated) - 2) + 2 * len(nontrivial)
    if lhs > rhs:
        raise PrimalDual2ECSSCertificateError(f"Impossible: Theorem 1.2 bound violated ({lhs} > {rhs})")
    if _parse_rat(cert["claimed_lhs"], "claimed_lhs") != lhs:
        raise PrimalDual2ECSSCertificateError(f"claimed_lhs mismatch: exact={lhs}")
    if _parse_rat(cert["claimed_rhs"], "claimed_rhs") != rhs:
        raise PrimalDual2ECSSCertificateError(f"claimed_rhs mismatch: exact={rhs}")

    return {
        "verified": True,
        "mode": cert["mode"],
        "L": len(leaves),
        "I": len(isolated),
        "C": len(nontrivial),
        "lhs": str(lhs),
        "rhs": str(rhs),
    }


def _verify_mode3_beta_optimality(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "beta", "claimed_branch1", "claimed_branch2",
        "claimed_alpha", "claimed_alpha_minus_1_sq",
    }
    if set(cert.keys()) != req:
        raise PrimalDual2ECSSCertificateError(f"Mode 3 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    beta = _parse_rat(cert["beta"], "beta")
    if not (Fraction(0, 1) < beta < Fraction(1, 2)):
        raise PrimalDual2ECSSCertificateError(f"Better-than-3 interior beta must lie in (0, 1/2), got {beta}")
    b1, b2, alpha = approx_ratio_exact(beta)
    if not (alpha < Fraction(3, 1)):
        raise PrimalDual2ECSSCertificateError("alpha(beta) >= 3")
    am1_sq = (alpha - Fraction(1, 1)) ** 2
    if am1_sq <= Fraction(3, 1):
        raise PrimalDual2ECSSCertificateError("Impossible: rational alpha beat irrational sqrt(3)+1")
    if _parse_rat(cert["claimed_branch1"], "claimed_branch1") != b1:
        raise PrimalDual2ECSSCertificateError("claimed_branch1 mismatch")
    if _parse_rat(cert["claimed_branch2"], "claimed_branch2") != b2:
        raise PrimalDual2ECSSCertificateError("claimed_branch2 mismatch")
    if _parse_rat(cert["claimed_alpha"], "claimed_alpha") != alpha:
        raise PrimalDual2ECSSCertificateError("claimed_alpha mismatch")
    if _parse_rat(cert["claimed_alpha_minus_1_sq"], "claimed_alpha_minus_1_sq") != am1_sq:
        raise PrimalDual2ECSSCertificateError("claimed_alpha_minus_1_sq mismatch")
    return {
        "verified": True,
        "mode": cert["mode"],
        "beta": str(beta),
        "alpha": str(alpha),
        "excess_sq_over_3": str(am1_sq - Fraction(3, 1)),
    }


def _verify_mode4_trace_telescoping(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema", "mode", "name", "n_vertices", "beta", "alpha",
        "steps", "claimed_total_pay", "claimed_total_earn",
    }
    if set(cert.keys()) != req:
        raise PrimalDual2ECSSCertificateError(f"Mode 4 key mismatch: {sorted(set(cert.keys()) ^ req)}")
    n = _parse_int(cert["n_vertices"], "n_vertices")
    if not (3 <= n <= 64):
        raise PrimalDual2ECSSCertificateError("n_vertices must be in [3, 64]")
    beta = _parse_rat(cert["beta"], "beta")
    if not (Fraction(0, 1) <= beta <= Fraction(1, 2)):
        raise PrimalDual2ECSSCertificateError("beta must lie in [0, 1/2]")
    _, _, expected_alpha = approx_ratio_exact(beta)
    alpha = _parse_rat(cert["alpha"], "alpha")
    if alpha != expected_alpha:
        raise PrimalDual2ECSSCertificateError(f"alpha={alpha} != expected {expected_alpha}")

    s_raw = cert["steps"]
    if type(s_raw) is not list or not s_raw or len(s_raw) > 2 * n - 2:
        raise PrimalDual2ECSSCertificateError(f"steps count must be in [1, {2*n - 2}] (Lemma 3.1)")

    prev_pot = 2 * n
    tot_pay = Fraction(0, 1)
    tot_earn = Fraction(0, 1)
    for idx, st in enumerate(s_raw):
        if type(st) is not dict or set(st.keys()) != {"num_nodes", "kappa", "L", "I", "C", "delta", "pay_step", "earn_step"}:
            raise PrimalDual2ECSSCertificateError(f"steps[{idx}] invalid keys")
        vn = _parse_int(st["num_nodes"], f"steps[{idx}].num_nodes")
        kp = _parse_int(st["kappa"], f"steps[{idx}].kappa")
        L = _parse_int(st["L"], f"steps[{idx}].L")
        I = _parse_int(st["I"], f"steps[{idx}].I")
        C = _parse_int(st["C"], f"steps[{idx}].C")
        dt = _parse_rat(st["delta"], f"steps[{idx}].delta")
        ps = _parse_rat(st["pay_step"], f"steps[{idx}].pay_step")
        es = _parse_rat(st["earn_step"], f"steps[{idx}].earn_step")
        if vn < 2 or vn > n or kp < 1 or L < 0 or I < 0 or C < 0 or L < 2 * C or dt < 0 or ps < 0 or es < 0:
            raise PrimalDual2ECSSCertificateError(f"steps[{idx}] invalid structural counts or negative values")
        if kp != I + C or I + 2 * C > vn or L + I > vn:
            raise PrimalDual2ECSSCertificateError(f"steps[{idx}] violates forest component/vertex invariants")
        if kp == 1 and not (I == 0 and C == 1):
            raise PrimalDual2ECSSCertificateError(f"steps[{idx}] connected forest requires I=0 and C=1")
        expected_es = (Fraction(L + 2 * I, 1) + 2 * beta * C) * dt if kp >= 2 else Fraction(L, 1) * dt
        if es != expected_es:
            raise PrimalDual2ECSSCertificateError(f"steps[{idx}] earn_step={es} != expected {expected_es} (Lemma 3.3)")
        pot = vn + kp
        if idx == 0:
            if pot != 2 * n:
                raise PrimalDual2ECSSCertificateError(f"Initial potential must be 2*n={2*n}, got {pot}")
        else:
            if not (pot <= prev_pot - 1):
                raise PrimalDual2ECSSCertificateError(f"Potential failed to strictly decrease at step {idx}")
        prev_pot = pot
        if ps > alpha * es:
            raise PrimalDual2ECSSCertificateError(f"Step {idx} violated Lemma 3.4 ratio: {ps} > {alpha} * {es}")
        tot_pay += ps
        tot_earn += es

    if tot_pay > alpha * tot_earn:
        raise PrimalDual2ECSSCertificateError("Telescoped sum violated approximation ratio")
    if _parse_rat(cert["claimed_total_pay"], "claimed_total_pay") != tot_pay:
        raise PrimalDual2ECSSCertificateError("claimed_total_pay mismatch")
    if _parse_rat(cert["claimed_total_earn"], "claimed_total_earn") != tot_earn:
        raise PrimalDual2ECSSCertificateError("claimed_total_earn mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n_vertices": n,
        "num_steps": len(s_raw),
        "total_pay": str(tot_pay),
        "total_earn": str(tot_earn),
        "alpha": str(alpha),
    }


def verify_primal_dual_2ecss_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    if type(cert) is not dict:
        raise PrimalDual2ECSSCertificateError("Certificate root must be a dict")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise PrimalDual2ECSSCertificateError(f"Invalid schema: {cert.get('schema')!r}")
    name = cert.get("name")
    if type(name) is not str or not name.strip():
        raise PrimalDual2ECSSCertificateError(f"Certificate name must be non-empty str, got {name!r}")
    mode = cert.get("mode")
    if mode == "primal_dual_2ecss_solution_exact":
        return _verify_mode1_solution(cert)
    if mode == "thm12_minimal_augmentation_exact":
        return _verify_mode2_thm12_aug(cert)
    if mode == "nonuniform_beta_ratio_optimality_exact":
        return _verify_mode3_beta_optimality(cert)
    if mode == "primal_dual_trace_telescoping_exact":
        return _verify_mode4_trace_telescoping(cert)
    raise PrimalDual2ECSSCertificateError(f"Unknown mode: {mode!r}")
