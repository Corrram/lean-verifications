# Coverage

**Status: in progress.** Blest normalization, range, mixtures, reflection symmetry, the xi=0 endpoint, and the entire xi=1 boundary are checked. The curved extremal family, its coefficient formulas, interior region and maximal gap remain pending.

## Source and conventions

Source: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
Journal reference: [DOI 10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744); version comparison pending.

Blest weights the first coordinate by 1-u, exactly as in equation (3). The product uniform measure is proved to give the displayed iterated integral. All integrals exist for arbitrary copulas, including singular ones. Xi conditions coordinate 1 on coordinate 0, with the derivative bridge checked in equation (2). Pi/M/W benchmarks and the full range [-1,1] are checked. Reflection of the second coordinate preserves xi and negates nu. This does not construct or verify the extremal family, and it makes no sign-reversal claim for reflection of the first coordinate.

The vertical boundary is obtained using the proved identity nu=rho for radially symmetric copulas and centered deterministic witnesses with rho=1-2 alpha^3. The curved extremal family is still a separate obligation.

## Result map

Proofs are in [Blest.lean](Blest.lean), [Normalization.lean](Normalization.lean), and [RightBoundary.lean](RightBoundary.lean), imported by
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
| Theorem 1.1: xi=0 endpoint | `Papers.Rockel2026XiBlest.xi_zero_slice` | verified | Xi=0 forces the unique copula Pi and nu=0; the xi=1 boundary is checked below; curved boundary points remain pending. |
| Supporting identity for Theorem 1.1 vertical boundary | `Papers.Rockel2026XiBlest.blest_eq_rho_of_radiallySymmetric` | verified | Blest nu equals Spearman rho for every radially symmetric copula. Both uniform-coordinate reflection and weighted-integral identities are proved. |
| Theorem 1.1: entire vertical boundary | `Papers.Rockel2026XiBlest.xi_one_slice` | verified | Exactly nu in [-1,1] is attainable at xi=1. Centered deterministic radially symmetric copulas supply the witnesses; no unproved curved-boundary formula is used. |
| Lemma 2.1 and the extremal copula family | — | pending | Construct the clamped conditional distributions and prove their marginal identities. |
| Theorem 2.3 and Section 4 coefficient formulas | — | pending | Derive the piecewise xi/Blest expressions and endpoint limits. |
| Theorem 1.1 beyond the xi=0 and xi=1 slices | — | pending | Prove the curved optimization bound, attainment, uniqueness, interior region and maximal gap. |
| Equation (3): reversed integration order | `Papers.Rockel2026XiBlest.blest_integral_formula_swapped` | verified | Fubini and integrability for the weighted CDF of every copula. |
| After equation (3): M/W normalization and range | `Papers.Rockel2026XiBlest.blest_comonotonic`; `Papers.Rockel2026XiBlest.blest_countermonotonic`; `Papers.Rockel2026XiBlest.blest_mem_Icc` | verified | Nu(M)=1, nu(W)=-1, and -1<=nu(C)<=1 for every copula. |
| Equation (13) and the following xi calculation | `Papers.Rockel2026XiBlest.blest_reflect_second`; `Papers.Rockel2026XiBlest.xi_blest_reflection` | verified | Reflecting coordinate 1 preserves xi and negates Blest's nu, including singular copulas. |
| Journal/preprint correspondence | — | pending | Only arXiv v1 is mapped. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
