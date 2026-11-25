"""Generate 3 publication-quality 300-DPI figures for Paper 25.
Author: Lluis Eriksson
"""
from __future__ import annotations

import json
import math
import pathlib

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULTS = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.0,
    "axes.labelsize": 9.2,
    "legend.fontsize": 7.3,
    "xtick.labelsize": 8.4,
    "ytick.labelsize": 8.4,
    "axes.grid": True,
    "grid.alpha": 0.28,
    "grid.linestyle": "--",
})


def make_fig1() -> None:
    d2 = json.loads((RESULTS / "exp2_beta_ratio_curve.json").read_text(encoding="utf-8"))
    d3 = json.loads((RESULTS / "exp3_rational_convergents.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): Dual-branch tradeoff curve alpha(beta) = max(2+2*beta, 2+1/(1+beta))
    r2 = d2["rows"]
    bs = [r["beta"] for r in r2]
    ax1.plot(bs, [r["branch1"] for r in r2], "--", color="#1b6ca8", lw=1.7, label=r"Branch 1: $2 + 2\beta$")
    ax1.plot(bs, [r["branch2"] for r in r2], "-.", color="#2a9d8f", lw=1.7, label=r"Branch 2: $2 + \frac{1}{1+\beta}$")
    ax1.plot(bs, [r["alpha"] for r in r2], "o-", color="#c1121f", lw=2.2, ms=3.8, label=r"Guarantee $\alpha(\beta) = \max(\cdot)$")
    b_star = (math.sqrt(3.0) - 1.0) / 2.0
    a_star = math.sqrt(3.0) + 1.0
    ax1.plot([b_star], [a_star], "*", color="#111111", ms=10.5, zorder=6,
             label=r"Optimum $\beta^* = \frac{\sqrt{3}-1}{2},\; \alpha^* = \sqrt{3}+1$")
    ax1.axhline(3.0, color="#555555", lw=1.1, ls=":")
    ax1.set_ylim(2.45, 3.12)
    ax1.set_xlabel(r"Nontrivial-component dual growth rate $\beta \in [0, 1/2]$")
    ax1.set_ylabel(r"Approximation ratio $\alpha(\beta)$")
    ax1.set_title(r"(a) Exact Non-Uniform Primal-Dual Tradeoff (Lemma 3.4)")
    ax1.legend(loc="lower center", frameon=True, framealpha=0.95, fontsize=6.9)

    # Panel (b): Continued-fraction rational convergents gap to sqrt(3)+1 (log scale)
    r3 = d3["rows"]
    labels = [r["beta_exact"] for r in r3]
    gaps = [r["gap_to_sqrt3_plus_1"] for r in r3]
    xs = np.arange(len(labels))
    ax2.semilogy(xs, gaps, "o-", color="#1b6ca8", lw=2.1, ms=6.0,
                 label=r"Exact rational excess $\alpha(\beta_k) - (\sqrt{3}+1)$")
    for x_v, g_v, r in zip(xs, gaps, r3):
        ax2.text(x_v, g_v * 1.95, r["alpha_exact"], ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax2.set_xticks(xs)
    ax2.set_xticklabels([f"b={l}" for l in labels], fontsize=7.6)
    ax2.set_xlim(-0.45, 5.45)
    ax2.set_ylim(1e-7, 2.5)
    ax2.set_xlabel(r"Rational growth rate convergent $\beta_k \in \mathbb{Q}$")
    ax2.set_ylabel(r"Gap $\alpha(\beta_k) - (\sqrt{3}+1)$ (log scale)")
    ax2.set_title(r"(b) Quadratic Rational Convergence to $\sqrt{3}+1$")
    ax2.legend(loc="lower left", frameon=True, framealpha=0.94, fontsize=7.2)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_beta_tradeoff_and_convergents.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d4 = json.loads((RESULTS / "exp4_empirical_primal_dual.json").read_text(encoding="utf-8"))
    rows = d4["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): Empirical primal/dual ratios on 4 weighted benchmarks (beta=0 vs beta=15/41)
    gnames = ["Prism-6", "Wheel-7\n(parallel)", "Barbell-8\n(clusters)", "TriCluster-9\n(3-comp)"]
    r_b0 = [r["ratio_b0"] for r in rows]
    r_opt = [r["ratio_opt"] for r in rows]
    x = np.arange(len(gnames))
    w = 0.34
    ax1.bar(x - w / 2, r_b0, width=w, color="#8d99ae", edgecolor="#222", lw=0.7, label=r"BCS20 ($\beta = 0$, bound $3$)")
    ax1.bar(x + w / 2, r_opt, width=w, color="#2a9d8f", edgecolor="#222", lw=0.7, label=r"Exact $\beta = 15/41$ (bound $153/56$)")
    ax1.axhline(153.0 / 56.0, color="#c1121f", lw=1.4, ls="--", label=r"Certified worst-case $153/56 \approx 2.732$")
    ax1.set_xticks(x)
    ax1.set_xticklabels(gnames, fontsize=7.8)
    ax1.set_ylim(0, 3.15)
    ax1.set_ylabel(r"Exact ratio $c(F) / \mathrm{Dual}(y, z)$")
    ax1.set_title(r"(a) Exact Primal/Dual Ratios on 2ECSS Benchmarks")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94, fontsize=7.0)

    # Panel (b): Lemma 3.1 actual iterations T vs theoretical bound 2n - 2
    iters = [r["iters_opt"] for r in rows]
    caps = [r["max_iters_2n_2"] for r in rows]
    ax2.bar(x - w / 2, iters, width=w, color="#1b6ca8", edgecolor="#222", lw=0.7, label=r"Actual primal-dual iterations $T$")
    ax2.bar(x + w / 2, caps, width=w, color="#e07a5f", edgecolor="#222", lw=0.7, label=r"Lemma 3.1 potential bound $2n - 2$")
    for xv, iv, cv in zip(x, iters, caps):
        ax2.text(xv - w / 2, iv + 0.3, str(iv), ha="center", va="bottom", fontsize=7.8, fontweight="bold")
        ax2.text(xv + w / 2, cv + 0.3, str(cv), ha="center", va="bottom", fontsize=7.8, fontweight="bold")
    ax2.set_xticks(x)
    ax2.set_xticklabels(gnames, fontsize=7.8)
    ax2.set_ylim(0, 19.5)
    ax2.set_ylabel(r"Iteration count $T$")
    ax2.set_title(r"(b) Lemma 3.1 Potential Bound ($T \leq 2n - 2$)")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.94, fontsize=7.2)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_empirical_ratios_and_iters.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RESULTS / "exp1_certified_atlas.json").read_text(encoding="utf-8"))
    rows = d1["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.95), dpi=300, gridspec_kw={"width_ratios": [1.62, 1.0]})

    mode_colors = {
        "primal_dual_2ecss_solution_exact": "#1b6ca8",
        "thm12_minimal_augmentation_exact": "#2a9d8f",
        "nonuniform_beta_ratio_optimality_exact": "#e07a5f",
        "primal_dual_trace_telescoping_exact": "#c1121f",
    }
    labels = [r["file"].replace(".cert.json", "") for r in rows]
    ms = [r["verify_ms"] for r in rows]
    cols = [mode_colors[r["mode"]] for r in rows]
    y = np.arange(len(rows))
    ax1.barh(y, ms, color=cols, edgecolor="#222", lw=0.6, height=0.68)
    ax1.set_yticks(y)
    ax1.set_yticklabels(labels, fontsize=6.2)
    ax1.invert_yaxis()
    ax1.set_xlabel(r"Exact-$\mathbb{Q}$ verification latency (ms)")
    ax1.set_title(r"(a) Zero-Float Replay Latency Across 16 Certificates")

    counts = [
        sum(1 for r in rows if r["mode"] == "primal_dual_2ecss_solution_exact"),
        sum(1 for r in rows if r["mode"] == "thm12_minimal_augmentation_exact"),
        sum(1 for r in rows if r["mode"] == "nonuniform_beta_ratio_optimality_exact"),
        sum(1 for r in rows if r["mode"] == "primal_dual_trace_telescoping_exact"),
    ]
    m_labels = ["Mode 1\nPrimal-Dual\n2ECSS", "Mode 2\nThm. 1.2\nAugment.", "Mode 3\nBeta\nRatio", "Mode 4\nTrace\nTelesc."]
    bars = ax2.bar(range(4), counts, color=["#1b6ca8", "#2a9d8f", "#e07a5f", "#c1121f"], edgecolor="#222", lw=0.7)
    for b, c in zip(bars, counts):
        ax2.text(b.get_x() + b.get_width() / 2.0, c + 0.15, str(c), ha="center", va="bottom", fontweight="bold", fontsize=8.5)
    ax2.set_xticks(range(4))
    ax2.set_xticklabels(m_labels, fontsize=7.6)
    ax2.set_ylabel("Certified instances")
    ax2.set_ylim(0, 5.4)
    ax2.set_title("(b) Coverage Across All 4 Modes")

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_atlas_summary.png", dpi=300)
    plt.close(fig)


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated all 3 publication figures in paper/figures/.")
