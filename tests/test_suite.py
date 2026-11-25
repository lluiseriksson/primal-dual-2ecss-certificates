"""Gate-2 verification, brute-force exact OPT 2ECSS cross-check, and 54-attack live red-team suite for Paper 25.
Author: Lluis Eriksson
"""
from __future__ import annotations

import copy
import json
import pathlib
import sys
from decimal import Decimal
from fractions import Fraction
from itertools import combinations

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from src.primal_dual_2ecss_certifier import (
    PrimalDual2ECSSCertificateError,
    verify_primal_dual_2ecss_certificate_exact,
)
from src.primal_dual_2ecss_exact import (
    approx_ratio_exact,
    is_2_edge_connected,
    run_primal_dual_2ecss_exact,
)

CERTS_DIR = ROOT / "results" / "certificates"


def test_bruteforce_exact_opt_and_weak_duality_cross_checks() -> None:
    """Independently enumerate ALL 2^11 = 2048 edge subsets of prism6_weighted to cross-check exact OPT == 18."""
    c1 = json.loads((CERTS_DIR / "pd_2ecss_prism6_weighted.cert.json").read_text(encoding="utf-8"))
    n = c1["n_vertices"]
    edges = [(e[0], e[1], Fraction(e[2])) for e in c1["edges"]]
    m = len(edges)
    assert m == 11

    best_opt = None
    for mask in range(1, 1 << m):
        sub_uv = [(edges[i][0], edges[i][1]) for i in range(m) if (mask >> i) & 1]
        if len(sub_uv) < n:
            continue
        cost = sum((edges[i][2] for i in range(m) if (mask >> i) & 1), Fraction(0, 1))
        if best_opt is not None and cost >= best_opt:
            continue
        if is_2_edge_connected(n, sub_uv):
            best_opt = cost

    assert best_opt == Fraction(18, 1)
    assert Fraction(c1["claimed_dual_obj"]) <= best_opt <= Fraction(c1["claimed_primal_cost"])
    # Verify continued-fraction convergents strictly improve toward sqrt(3) + 1
    alphas = [approx_ratio_exact(b)[2] for b in (Fraction(0), Fraction(1, 3), Fraction(4, 11), Fraction(15, 41), Fraction(56, 153))]
    for i in range(len(alphas) - 1):
        assert alphas[i + 1] < alphas[i]
    assert alphas[-1] == Fraction(571, 209)


def test_all_16_certificates_verify_cleanly() -> None:
    files = sorted(CERTS_DIR.glob("*.cert.json"))
    assert len(files) == 16
    for f in files:
        res = verify_primal_dual_2ecss_certificate_exact(json.loads(f.read_text(encoding="utf-8")))
        assert res["verified"] is True


def test_54_live_adversarial_red_team_attacks_rejected() -> None:
    c1 = json.loads((CERTS_DIR / "pd_2ecss_prism6_weighted.cert.json").read_text(encoding="utf-8"))
    c2 = json.loads((CERTS_DIR / "thm12_two_paths6_b1_3.cert.json").read_text(encoding="utf-8"))
    c3 = json.loads((CERTS_DIR / "beta_conv_15_41.cert.json").read_text(encoding="utf-8"))
    c4 = json.loads((CERTS_DIR / "trace_prism6_weighted.cert.json").read_text(encoding="utf-8"))

    attacks = []

    def add(name, base, fn):
        cand = copy.deepcopy(base)
        fn(cand)
        attacks.append((name, cand))

    # Group A: Schema, Types & Canonical Rationals (16 attacks)
    attacks.append(("01_root_not_dict", ["bad"]))
    add("02_wrong_schema", c1, lambda x: x.__setitem__("schema", "PRIMAL-DUAL-2ECSS-CERT-9.9"))
    add("03_unknown_mode", c1, lambda x: x.__setitem__("mode", "bogus"))
    add("04_extra_key", c1, lambda x: x.__setitem__("evil", 1))
    add("05_missing_key", c1, lambda x: x.pop("beta"))
    add("06_float_injection", c3, lambda x: x.__setitem__("beta", 0.366))
    add("07_bool_injection", c1, lambda x: x.__setitem__("n_vertices", True))
    add("08_decimal_injection", c3, lambda x: x.__setitem__("beta", Decimal("0.33")))
    add("09_complex_injection", c3, lambda x: x.__setitem__("beta", 1 + 0j))
    add("10_tuple_injection", c1, lambda x: x.__setitem__("solution_edge_indices", tuple(x["solution_edge_indices"])))
    add("11_non_str_key", c1, lambda x: x.__setitem__(99, "bad"))
    add("12_unreduced_frac", c3, lambda x: x.__setitem__("beta", "30/82"))
    add("13_denom_one_frac", c1, lambda x: x.__setitem__("claimed_primal_cost", "18/1"))
    add("14_neg_zero", c1, lambda x: x["dual_z"].__setitem__(0, "-0"))
    add("15_non_str_name", c1, lambda x: x.__setitem__("name", 123))
    add("16_empty_name", c1, lambda x: x.__setitem__("name", "  "))

    # Group B: Mode 1 Primal-Dual 2ECSS Solution Forgeries (13 attacks)
    add("17_n_below_3", c1, lambda x: x.__setitem__("n_vertices", 2))
    add("18_beta_above_half", c1, lambda x: x.__setitem__("beta", "3/5"))
    add("19_self_loop_edge", c1, lambda x: x["edges"].__setitem__(0, [0, 0, "2"]))
    add("20_negative_edge_cost", c1, lambda x: x["edges"].__setitem__(0, [0, 1, "-2"]))
    add("21_drop_edge_breaks_2ec", c1, lambda x: x["solution_edge_indices"].pop())
    add("22_add_redundant_edge_not_minimal", c1, lambda x: (
        x["solution_edge_indices"].append(next(i for i in range(len(x["edges"])) if i not in x["solution_edge_indices"]))
    ))
    add("23_duplicate_sol_edge", c1, lambda x: x["solution_edge_indices"].append(x["solution_edge_indices"][0]))
    add("24_negative_dual_z", c1, lambda x: x["dual_z"].__setitem__(0, "-1"))
    add("25_improper_full_cut_S", c1, lambda x: x["dual_cuts"].append([[0, 1, 2, 3, 4, 5], "1"]))
    add("26_zero_dual_y", c1, lambda x: x["dual_cuts"][0].__setitem__(1, "0"))
    add("27_inflate_y_breaks_constraint_3b", c1, lambda x: x["dual_cuts"][0].__setitem__(1, "100"))
    add("28_forged_primal_cost", c1, lambda x: x.__setitem__("claimed_primal_cost", "17"))
    add("29_forged_alpha_bound", c1, lambda x: x.__setitem__("claimed_alpha_bound", "2"))

    # Group C: Mode 2 Theorem 1.2 Minimal Augmentation Forgeries (9 attacks)
    add("30_cycle_in_forest", c2, lambda x: x["forest_edges"].append([0, 2]))
    add("31_empty_augmentation", c2, lambda x: x.__setitem__("augmentation_edges", []))
    add("32_aug_not_2ec", c2, lambda x: x["augmentation_edges"].pop())
    add("33_aug_not_minimal", c2, lambda x: x["augmentation_edges"].append([1, 4]))
    add("34_forged_lhs", c2, lambda x: x.__setitem__("claimed_lhs", "1"))
    add("35_forged_rhs", c2, lambda x: x.__setitem__("claimed_rhs", "100"))
    add("36_beta_negative_mode2", c2, lambda x: x.__setitem__("beta", "-1/3"))
    add("37_self_loop_forest", c2, lambda x: x["forest_edges"].append([0, 0]))
    add("38_out_of_range_vertex_aug", c2, lambda x: x["augmentation_edges"].append([0, 99]))

    # Group D: Mode 3 Non-Uniform Beta Optimality Forgeries (7 attacks)
    add("39_beta_zero_not_strictly_below_3", c3, lambda x: x.__setitem__("beta", "0"))
    add("40_beta_half_not_strictly_below_3", c3, lambda x: x.__setitem__("beta", "1/2"))
    add("41_forged_branch1", c3, lambda x: x.__setitem__("claimed_branch1", "2"))
    add("42_forged_branch2", c3, lambda x: x.__setitem__("claimed_branch2", "2"))
    add("43_forged_alpha_mode3", c3, lambda x: x.__setitem__("claimed_alpha", "5/2"))
    add("44_forged_alpha_minus_1_sq", c3, lambda x: x.__setitem__("claimed_alpha_minus_1_sq", "3"))
    add("45_beta_above_half_mode3", c3, lambda x: x.__setitem__("beta", "3/4"))

    # Group E: Mode 4 Primal-Dual Trace Telescoping Forgeries (9 attacks)
    add("46_empty_steps", c4, lambda x: x.__setitem__("steps", []))
    add("47_too_many_steps_gt_2n_2", c4, lambda x: x.__setitem__("steps", x["steps"] + x["steps"]))
    add("48_wrong_initial_potential", c4, lambda x: x["steps"][0].__setitem__("num_nodes", 5))
    add("49_potential_fails_to_decrease", c4, lambda x: x["steps"][1].__setitem__("kappa", x["steps"][0]["kappa"]))
    add("50_leaves_below_2C", c4, lambda x: (x["steps"][0].__setitem__("C", 2), x["steps"][0].__setitem__("L", 3)))
    add("51_step_ratio_violated", c4, lambda x: x["steps"][0].__setitem__("pay_step", "999"))
    add("52_negative_pay_step", c4, lambda x: x["steps"][0].__setitem__("pay_step", "-1"))
    add("53_forged_total_pay", c4, lambda x: x.__setitem__("claimed_total_pay", "1"))
    add("54_wrong_alpha_mode4", c4, lambda x: x.__setitem__("alpha", "2"))
    # Group F: Mode 4 Lemma 3.3 earn_step & Forest Structural Invariant Forgeries (3 attacks -> 57 total!)
    add("55_forged_earn_at_delta_zero", c4, lambda x: (
        x["steps"][0].__setitem__("delta", "0"),
        x["steps"][0].__setitem__("earn_step", "100"),
    ))
    add("56_num_nodes_exceeds_n", c4, lambda x: (
        x.__setitem__("n_vertices", 4),
        x.__setitem__("steps", [{
            "num_nodes": 7, "kappa": 1, "L": 0, "I": 0, "C": 0,
            "delta": "0", "pay_step": "0", "earn_step": "0",
        }]),
        x.__setitem__("claimed_total_pay", "0"),
        x.__setitem__("claimed_total_earn", "0"),
    ))
    add("57_kappa_neq_I_plus_C", c4, lambda x: (
        x["steps"][0].__setitem__("I", x["steps"][0]["I"] - 1),
    ))

    assert len(attacks) == 57
    for name, cand in attacks:
        with pytest.raises(PrimalDual2ECSSCertificateError):
            verify_primal_dual_2ecss_certificate_exact(cand)
