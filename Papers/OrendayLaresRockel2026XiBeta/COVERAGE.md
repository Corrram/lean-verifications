# Coverage

**Status: in progress.** Theorem 1 is checked: the exact xi-beta region, both attaining boundaries, and uniqueness of the lower boundary. Density and further structural properties of the tent family, classical rank formulas, and Section 6 subclasses remain pending.

## Source and conventions

Source: [arXiv:2606.30033v1](https://arxiv.org/abs/2606.30033v1), 29 June 2026.

Beta is 4 C(1/2,1/2)-1, and xi conditions coordinate 1 on coordinate 0. The universal bound is proved with regular conditional distributions, without a density assumption. The left boundary is the source's signed tent family. The right boundary uses an alternative deterministic witness: the ordinal sum of two countermonotonic copulas, split at (1+b)/4. Its existence proves the right-boundary assertion in Theorem 1; it does not establish the radial-symmetry or quadrant-dependence properties of the particular shuffle in Proposition 6. Fixed-beta mixtures of these explicitly constructed endpoints prove every attainable pair. Uniqueness of the lower boundary follows from strict convexity of xi. Both parameter endpoints are included.

## Result map

Proofs are in [SharpBound.lean](SharpBound.lean), [LeftBoundary.lean](LeftBoundary.lean),
[RightBoundary.lean](RightBoundary.lean), [Mixtures.lean](Mixtures.lean), and
[Region.lean](Region.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (1): derivative convention | `Papers.OrendayLaresRockel2026XiBeta.xi_derivative_formula` | verified | All bivariate copulas; no density assumption. |
| Section 5, proof of Theorem 1: continuity along mixtures | `Papers.OrendayLaresRockel2026XiBeta.xi_mixture_continuous` | verified | Any pair of copulas; proved from the exact quadratic identity. |
| Section 5, proof of Theorem 1: beta stays fixed | `Papers.OrendayLaresRockel2026XiBeta.beta_mixture_fixed` | verified | Both input copulas have the same prescribed beta. |
| Section 5, proof of Theorem 1: intermediate-value step | `Papers.OrendayLaresRockel2026XiBeta.fixed_beta_intermediate` | verified | Supplied copulas with equal beta and xi values bracketing the target; the full-region theorem supplies the proved boundary constructions below. |
| Proposition 5: displacement regularity | `Papers.OrendayLaresRockel2026XiBeta.medianDisplacement_lipschitz` | verified | The median conditional displacement is 1-Lipschitz for every copula. |
| Proposition 5: two-strip energy bound | `Papers.OrendayLaresRockel2026XiBeta.median_strip_energy`; `Papers.OrendayLaresRockel2026XiBeta.median_energy_le_xi` | verified | Jensen estimates on both median strips, integrated against the uniform response marginal. |
| Proposition 5: tent comparison | `Papers.OrendayLaresRockel2026XiBeta.medianTent_le_abs_displacement` | verified | The absolute median displacement dominates the tent of height abs(beta)/2. |
| Proposition 5: universal sharp inequality | `Papers.OrendayLaresRockel2026XiBeta.beta_cubic_le_two_xi` | verified | abs(beta)^3 <= 2 xi for every copula, including singular laws. |
| Equations (4)-(6): boundary copula construction | `Papers.OrendayLaresRockel2026XiBeta.leftBoundary_cdf` | verified | Genuine copula with the source signed tent CDF; all b in [-1,1]. |
| Proposition 3(i): left-boundary values | `Papers.OrendayLaresRockel2026XiBeta.leftBoundary_beta`; `Papers.OrendayLaresRockel2026XiBeta.leftBoundary_xi`; `Papers.OrendayLaresRockel2026XiBeta.left_boundary_attained` | verified | Constructs beta=b and xi=abs(b)^3/2, with no assumed endpoints. |
| Proposition 5: equality characterization | `Papers.OrendayLaresRockel2026XiBeta.xi_eq_lower_iff` | verified | At fixed beta=b, equality holds if and only if the copula is the signed tent copula L_b. |
| Theorem 1: deterministic right-boundary witness | `Papers.OrendayLaresRockel2026XiBeta.xi_twoBlockFlip`; `Papers.OrendayLaresRockel2026XiBeta.rightBoundary_beta`; `Papers.OrendayLaresRockel2026XiBeta.rightBoundary_xi`; `Papers.OrendayLaresRockel2026XiBeta.right_boundary_attained` | verified | Alternative two-block decreasing shuffle attains xi=1 at every b in [-1,1]; no subclass claims. |
| Theorem 1: exact attainable region | `Papers.OrendayLaresRockel2026XiBeta.exact_xi_beta_region` | verified | A pair (x,b) is attained iff 0<=x<=1, -1<=b<=1, and abs(b)^3<=2x. Both directions and all boundary cases are proved. |
| Proposition 2 and Proposition 3(ii)-(ix) beyond the boundary values | — | pending | Density, quadrant masses, reflection/radial symmetry, stochastic and total positivity properties, exchangeability, and rho/tau formulas. |
| Proposition 6: the source's particular shuffle and its subclass properties | — | pending | Theorem 1 right-boundary existence is proved above with a different witness. |
| Section 6: exact regions for subclasses | — | pending | Radially symmetric, quadrant-dependent and other restricted classes require separate witnesses and constraints. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
