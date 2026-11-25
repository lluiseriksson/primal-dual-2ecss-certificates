# Machine-Checked Exact-Rational Primal-Dual Cut-Covering and Better-Than-3 Approximation Certificates for 2-Edge-Connected Spanning Subgraphs

**Author:** Lluis Eriksson (with transparent AI assistance via Google Antigravity)  
**License:** MIT (code, Lean 4 proofs, certificates) / CC-BY-4.0 (manuscript)

Zero-dependency Lean 4 formalization, zero-float exact-$\mathbb{Q}$ primal-dual 2ECSS solver, and certificate verifier (`PRIMAL-DUAL-2ECSS-CERT-1.0`) for Danciu and Ibrahimpur (*Better-than-3 Approximation for 2ECSS Using the Primal-Dual Method*, `arXiv:2611.32924`, November 25, 2026).

## Verification Summary
- **Lean 4 Kernel (`lean/PrimalDual2ECSS.lean`, Lean 4.35.0):** 18/18 theorems, 0 warnings, 0 `sorry`, 0 `Classical.choice`, 5 zero-axiom theorems (`bcs20_beta_zero_ratio_3`, `endpoint_beta_half_ratio_3`, `rational_convergent_11_4_bound`, `rational_convergent_153_56_bound`, `rational_convergent_571_209_bound`), including full cleared Lemma 3.4 disconnected-forest ratio proof, inductive $T \le 2n - 2$ potential termination, inductive Cut-LP weak duality, and inductive iteration telescoping.
- **Exact-$\mathbb{Q}$ Solver & Certificate Atlas (`results/certificates/*.cert.json`):** 16 canonical certificates across 4 modes (exact primal-dual 2ECSS solutions with cut-LP duals $(y,z)$; exact Theorem 1.2 minimal-augmentation witnesses; rational $\beta_k$ better-than-3 optimality certificates; full iteration-trace telescoping audits), replayed with zero floats in `0.036`–`0.424 ms`.
- **Cross-Checks & Red-Team Suite (`tests/test_suite.py`):** Exhaustive $2^{11} = 2{,}048$-subset brute-force OPT check on `prism6_weighted` ($\mathrm{OPT} = 18 = \mathrm{Dual} = \mathrm{Primal}$), 16/16 certificate replays, and **57/57** live adversarial attacks rejected.

## One-Command Reproducibility
```bash
python scripts/verify_all.py
```
To regenerate all certificates, experiment JSONs, and 300-DPI figures from scratch:
```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```
