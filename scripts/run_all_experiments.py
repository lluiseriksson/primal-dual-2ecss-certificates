"""Generate all 16 canonical PRIMAL-DUAL-2ECSS-CERT-1.0 certificates and 4 experiment JSONs for Paper 25.
Author: Lluis Eriksson
"""
from __future__ import annotations

import json
import math
import pathlib
import sys
import time
from fractions import Fraction
from typing import Dict, List, Tuple

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.primal_dual_2ecss_certifier import verify_primal_dual_2ecss_certificate_exact
from src.primal_dual_2ecss_exact import (
    approx_ratio_exact,
    fmt_rat,
    is_forest_and_decompose,
    run_primal_dual_2ecss_exact,
)

RESULTS = ROOT / "results"
CERTS = RESULTS / "certificates"
RESULTS.mkdir(parents=True, exist_ok=True)
CERTS.mkdir(parents=True, exist_ok=True)


def _emit_cert(filename: str, cert: Dict) -> Dict:
    t0 = time.perf_counter()
    summary = verify_primal_dual_2ecss_certificate_exact(cert)
    ms = (time.perf_counter() - t0) * 1000.0
    (CERTS / filename).write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
    return {"file": filename, "mode": cert["mode"], "verify_ms": round(ms, 4), "summary": summary}


def _build_graph_instances() -> Dict[str, Tuple[int, List[Tuple[int, int, Fraction]]]]:
    """Four diverse weighted 2ECSS multigraph instances (including parallel edges, bridges, and tight-ratio gadgets)."""
    # 1. 6-vertex prism-chord multigraph with non-uniform costs
    g1 = (
        6,
        [
            (0, 1, Fraction(2)), (1, 2, Fraction(2)), (2, 0, Fraction(3)),
            (3, 4, Fraction(2)), (4, 5, Fraction(2)), (5, 3, Fraction(3)),
            (0, 3, Fraction(5)), (1, 4, Fraction(6)), (2, 5, Fraction(5)),
            (0, 4, Fraction(7)), (1, 5, Fraction(8)),
        ],
    )
    # 2. 7-vertex wheel-plus-parallel-edge multigraph
    g2 = (
        7,
        [
            (0, 1, Fraction(3)), (1, 2, Fraction(4)), (2, 3, Fraction(3)),
            (3, 4, Fraction(5)), (4, 5, Fraction(3)), (5, 6, Fraction(4)), (6, 0, Fraction(3)),
            (0, 2, Fraction(5)), (2, 4, Fraction(6)), (4, 6, Fraction(5)),
            (1, 5, Fraction(7)), (0, 3, Fraction(6)), (3, 6, Fraction(6)),
            (0, 1, Fraction(4)),  # parallel edge!
        ],
    )
    # 3. 8-vertex two-cluster barbell with sparse bridge links (stresses nontrivial component beta growth!)
    g3 = (
        8,
        [
            (0, 1, Fraction(1)), (1, 2, Fraction(1)), (2, 3, Fraction(1)), (3, 0, Fraction(4)),
            (0, 2, Fraction(3)), (1, 3, Fraction(3)),
            (4, 5, Fraction(1)), (5, 6, Fraction(1)), (6, 7, Fraction(1)), (7, 4, Fraction(4)),
            (4, 6, Fraction(3)), (5, 7, Fraction(3)),
            (0, 4, Fraction(6)), (1, 5, Fraction(7)), (2, 6, Fraction(6)), (3, 7, Fraction(8)),
        ],
    )
    # 4. 9-vertex three-component cluster network (3 disjoint cheap paths + expensive inter-cluster chords)
    g4 = (
        9,
        [
            (0, 1, Fraction(1)), (1, 2, Fraction(1)), (0, 2, Fraction(5)),
            (3, 4, Fraction(1)), (4, 5, Fraction(1)), (3, 5, Fraction(5)),
            (6, 7, Fraction(1)), (7, 8, Fraction(1)), (6, 8, Fraction(5)),
            (0, 3, Fraction(4)), (2, 5, Fraction(4)), (3, 6, Fraction(4)),
            (5, 8, Fraction(4)), (6, 0, Fraction(4)), (8, 2, Fraction(4)),
            (1, 4, Fraction(6)), (4, 7, Fraction(6)), (7, 1, Fraction(6)),
        ],
    )
    return {
        "prism6_weighted": g1,
        "wheel7_parallel": g2,
        "barbell8_clusters": g3,
        "tricluster9_network": g4,
    }


def main() -> None:
    graphs = _build_graph_instances()
    beta_opt_q = Fraction(15, 41)  # alpha = 153/56 = 2.73214 < 2.7322 < 3!
    atlas_rows = []
    solved = {}

    # =========================================================================
    # MODE 1: 4 Exact Primal-Dual 2ECSS Solution + Cut-LP Dual Certificates
    # =========================================================================
    betas_m1 = [Fraction(1, 3), Fraction(4, 11), Fraction(15, 41), Fraction(56, 153)]
    for (gname, (n, edges)), beta in zip(graphs.items(), betas_m1):
        res = run_primal_dual_2ecss_exact(n, edges, beta)
        solved[gname] = (n, edges, beta, res)
        _, _, alpha = approx_ratio_exact(beta)
        cert = {
            "schema": "PRIMAL-DUAL-2ECSS-CERT-1.0",
            "mode": "primal_dual_2ecss_solution_exact",
            "name": f"mode1_{gname}",
            "n_vertices": n,
            "edges": [[u, v, fmt_rat(c)] for (u, v, c) in edges],
            "beta": fmt_rat(beta),
            "solution_edge_indices": res["final_F"],
            "dual_cuts": [[list(S), fmt_rat(yv)] for S, yv in res["y_duals"].items()],
            "dual_z": [fmt_rat(zv) for zv in res["z_duals"]],
            "claimed_primal_cost": fmt_rat(res["primal_cost"]),
            "claimed_dual_obj": fmt_rat(res["dual_obj"]),
            "claimed_alpha_bound": fmt_rat(alpha),
        }
        atlas_rows.append(_emit_cert(f"pd_2ecss_{gname}.cert.json", cert))

    # =========================================================================
    # MODE 2: 4 Exact Theorem 1.2 Minimal-Augmentation Certificates
    # =========================================================================
    aug_cases = [
        (
            "thm12_two_paths6_b1_3.cert.json",
            "mode2_two_paths6",
            6,
            [(0, 1), (1, 2), (3, 4), (4, 5)],
            [(0, 3), (2, 5), (0, 5), (2, 3)],
            Fraction(1, 3),
        ),
        (
            "thm12_star_plus_iso7_b4_11.cert.json",
            "mode2_star_plus_iso7",
            7,
            [(0, 1), (0, 2), (0, 3), (4, 5)],
            [(1, 4), (2, 5), (3, 6), (6, 4), (1, 2)],
            Fraction(4, 11),
        ),
        (
            "thm12_three_comp8_b15_41.cert.json",
            "mode2_three_comp8",
            8,
            [(0, 1), (2, 3), (4, 5), (5, 6)],
            [(0, 2), (1, 4), (3, 6), (0, 7), (7, 6), (1, 3)],
            Fraction(15, 41),
        ),
        (
            "thm12_connected_tree6_b0.cert.json",
            "mode2_connected_tree6",
            6,
            [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5)],
            [(3, 4), (4, 5), (3, 5)],
            Fraction(0, 1),
        ),
    ]
    # Note: make sure each augmentation A is strictly minimal by running exact reverse-delete if needed!
    from src.primal_dual_2ecss_exact import is_2_edge_connected
    for fname, cname, n, f_e, a_e, beta in aug_cases:
        min_a = list(a_e)
        for idx in range(len(min_a) - 1, -1, -1):
            cand = min_a[:idx] + min_a[idx + 1:]
            if is_2_edge_connected(n, f_e + cand):
                min_a = cand
        ok, leaves, isolated, nontrivial = is_forest_and_decompose(n, f_e)
        assert ok
        li = set(leaves) | set(isolated)
        lhs_li = sum((1 if u in li else 0) + (1 if v in li else 0) for (u, v) in min_a)
        lhs_c = sum(sum(1 for (u, v) in min_a if (u in set(c)) != (v in set(c))) for c in nontrivial)
        lhs = Fraction(lhs_li, 1) + beta * lhs_c
        rhs = 2 * (1 + beta) * (len(leaves) + 2 * len(isolated) - 2) + 2 * len(nontrivial)
        cert = {
            "schema": "PRIMAL-DUAL-2ECSS-CERT-1.0",
            "mode": "thm12_minimal_augmentation_exact",
            "name": cname,
            "n_vertices": n,
            "forest_edges": [[u, v] for (u, v) in f_e],
            "augmentation_edges": [[u, v] for (u, v) in min_a],
            "beta": fmt_rat(beta),
            "claimed_lhs": fmt_rat(lhs),
            "claimed_rhs": fmt_rat(rhs),
        }
        atlas_rows.append(_emit_cert(fname, cert))

    # =========================================================================
    # MODE 3: 4 Non-Uniform Beta Better-Than-3 Rational Convergent Certificates
    # =========================================================================
    conv_betas = [
        ("beta_conv_1_3.cert.json", "mode3_beta_1_3", Fraction(1, 3)),
        ("beta_conv_4_11.cert.json", "mode3_beta_4_11", Fraction(4, 11)),
        ("beta_conv_15_41.cert.json", "mode3_beta_15_41", Fraction(15, 41)),
        ("beta_conv_56_153.cert.json", "mode3_beta_56_153", Fraction(56, 153)),
    ]
    for fname, cname, beta in conv_betas:
        b1, b2, alpha = approx_ratio_exact(beta)
        cert = {
            "schema": "PRIMAL-DUAL-2ECSS-CERT-1.0",
            "mode": "nonuniform_beta_ratio_optimality_exact",
            "name": cname,
            "beta": fmt_rat(beta),
            "claimed_branch1": fmt_rat(b1),
            "claimed_branch2": fmt_rat(b2),
            "claimed_alpha": fmt_rat(alpha),
            "claimed_alpha_minus_1_sq": fmt_rat((alpha - 1) ** 2),
        }
        atlas_rows.append(_emit_cert(fname, cert))

    # =========================================================================
    # MODE 4: 4 Full Primal-Dual Iteration-Trace Telescoping Certificates
    # =========================================================================
    for gname, (n, edges, beta, res) in solved.items():
        _, _, alpha = approx_ratio_exact(beta)
        steps_out = []
        tot_p = Fraction(0, 1)
        tot_e = Fraction(0, 1)
        for st in res["trace"]:
            tot_p += st["pay_step"]
            tot_e += st["earn_step"]
            steps_out.append({
                "num_nodes": st["num_nodes"],
                "kappa": st["kappa"],
                "L": st["L"],
                "I": st["I"],
                "C": st["C"],
                "delta": fmt_rat(st["delta"]),
                "pay_step": fmt_rat(st["pay_step"]),
                "earn_step": fmt_rat(st["earn_step"]),
            })
        cert = {
            "schema": "PRIMAL-DUAL-2ECSS-CERT-1.0",
            "mode": "primal_dual_trace_telescoping_exact",
            "name": f"mode4_trace_{gname}",
            "n_vertices": n,
            "beta": fmt_rat(beta),
            "alpha": fmt_rat(alpha),
            "steps": steps_out,
            "claimed_total_pay": fmt_rat(tot_p),
            "claimed_total_earn": fmt_rat(tot_e),
        }
        atlas_rows.append(_emit_cert(f"trace_{gname}.cert.json", cert))

    (RESULTS / "exp1_certified_atlas.json").write_text(
        json.dumps({"experiment": "exp1_certified_atlas", "count": len(atlas_rows), "rows": atlas_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 2: Tradeoff Curve alpha(beta) = max(2+2*beta, 2+1/(1+beta)) across [0, 1/2]
    # =========================================================================
    exp2_rows = []
    for k in range(0, 21):
        beta = Fraction(k, 40)
        b1, b2, alpha = approx_ratio_exact(beta)
        exp2_rows.append({
            "beta_exact": fmt_rat(beta),
            "beta": round(float(beta), 5),
            "branch1": round(float(b1), 6),
            "branch2": round(float(b2), 6),
            "alpha": round(float(alpha), 6),
        })
    (RESULTS / "exp2_beta_ratio_curve.json").write_text(
        json.dumps({"experiment": "exp2_beta_ratio_curve", "rows": exp2_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 3: Continued-Fraction Convergents of beta* = (sqrt(3)-1)/2 -> sqrt(3)+1
    # =========================================================================
    sqrt3_p1 = math.sqrt(3.0) + 1.0
    exp3_rows = []
    for beta in [Fraction(0, 1), Fraction(1, 3), Fraction(4, 11), Fraction(15, 41), Fraction(56, 153), Fraction(209, 571)]:
        b1, b2, alpha = approx_ratio_exact(beta)
        exp3_rows.append({
            "beta_exact": fmt_rat(beta),
            "alpha_exact": fmt_rat(alpha),
            "alpha_float": round(float(alpha), 8),
            "gap_to_sqrt3_plus_1": round(float(alpha) - sqrt3_p1, 9),
        })
    (RESULTS / "exp3_rational_convergents.json").write_text(
        json.dumps({"experiment": "exp3_rational_convergents", "rows": exp3_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # =========================================================================
    # EXP 4: Empirical Primal/Dual Ratios on Benchmark Graphs (beta=0 vs beta=15/41)
    # =========================================================================
    exp4_rows = []
    for gname, (n, edges) in graphs.items():
        r0 = run_primal_dual_2ecss_exact(n, edges, Fraction(0, 1))
        ro = run_primal_dual_2ecss_exact(n, edges, beta_opt_q)
        exp4_rows.append({
            "graph": gname,
            "n_vertices": n,
            "primal_b0": fmt_rat(r0["primal_cost"]),
            "dual_b0": fmt_rat(r0["dual_obj"]),
            "ratio_b0": round(float(r0["primal_cost"] / r0["dual_obj"]), 5),
            "primal_opt": fmt_rat(ro["primal_cost"]),
            "dual_opt": fmt_rat(ro["dual_obj"]),
            "ratio_opt": round(float(ro["primal_cost"] / ro["dual_obj"]), 5),
            "iters_opt": ro["iterations"],
            "max_iters_2n_2": 2 * n - 2,
        })
    (RESULTS / "exp4_empirical_primal_dual.json").write_text(
        json.dumps({"experiment": "exp4_empirical_primal_dual", "rows": exp4_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    print(f"[PASS] Generated & verified {len(atlas_rows)}/16 exact-Q certificates and 4 experiment JSONs.")
    for r in atlas_rows:
        print(f"  {r['file']:44s} {r['verify_ms']:6.3f} ms  {r['summary']}")


if __name__ == "__main__":
    main()
