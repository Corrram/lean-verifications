# Coverage

**Status: in progress.** Blest's weighted-CDF convention, monotonicity, affine mixtures, independence normalization, and the xi=0 endpoint are checked. The extremal family and exact region remain pending.

## Source and conventions

Source: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
Journal reference: [DOI 10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744); version comparison pending.

Blest weights the first coordinate by 1-u, exactly as in equation (3). The product uniform measure is proved to give the displayed iterated integral. All integrals exist for arbitrary copulas, including singular ones. Xi conditions coordinate 1 on coordinate 0, with the derivative bridge checked in equation (2). Only the independence normalization is covered; M/W benchmarks, the reflected boundary family and the global range are not claimed by the rows below.

## Result map

Proofs are in [Blest.lean](Blest.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (3): existence of the weighted integral | `Papers.Rockel2026XiBlest.blest_integrable` | verified | All bivariate copulas; no density hypothesis. |
| Equation (3): iterated-integral correspondence | `Papers.Rockel2026XiBlest.blest_integral_formula` | verified | First-coordinate weight 1-u and source integration order. |
| Equation (2): xi derivative convention | `Papers.Rockel2026XiBlest.xi_derivative_formula` | verified | All bivariate copulas; almost-everywhere derivative correspondence. |
| After equation (3): concordance monotonicity | `Papers.Rockel2026XiBlest.blest_mono` | verified | Pointwise CDF ordering implies ordering of Blest coefficients. |
| Equation (3): affine-mixture identity used in the region argument | `Papers.Rockel2026XiBlest.blest_mix` | verified | Any two copulas and every closed-interval mixture weight. |
| After equation (3): independence normalization | `Papers.Rockel2026XiBlest.blest_independence` | verified | Nu(Pi)=0 with the source normalization. |
| Theorem 1.1: xi=0 endpoint | `Papers.Rockel2026XiBlest.xi_zero_slice` | verified | Xi=0 forces the unique copula Pi and nu=0; other boundary points remain pending. |
| Lemma 2.1 and the extremal copula family | — | pending | Construct the clamped conditional distributions and prove their marginal identities. |
| Theorem 2.3 and Section 4 coefficient formulas | — | pending | Derive the piecewise xi/Blest expressions and endpoint limits. |
| Theorem 1.1 beyond the zero endpoint | — | pending | Prove the optimization bound, attainment, uniqueness, full region and maximal gap. |
| Remaining normalization and symmetry claims | — | pending | M/W values, global range and reflection correspondence remain outside the checked subset. |
| Journal/preprint correspondence | — | pending | Only arXiv v1 is mapped. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
