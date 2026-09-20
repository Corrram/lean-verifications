# Coverage

**Status: in progress.** The derivative convention and the fixed-beta interpolation step of Theorem 1 are checked. The sharp inequality and the left/right boundary constructions remain pending.

## Source and conventions

Source: [arXiv:2606.30033v1](https://arxiv.org/abs/2606.30033v1), 29 June 2026.

Beta is 4 C(1/2,1/2)-1, and xi conditions coordinate 1 on coordinate 0. Mixture weights are constant because copula marginals are uniform. The interpolation theorem assumes two actual copulas with equal beta and bracketing xi values, then constructs a mixture attaining the requested intermediate xi. It does not assume or conclude that the required sharp boundary copulas already exist. Singular copulas and endpoint weights are allowed.

## Result map

Proofs are in [Mixtures.lean](Mixtures.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (1): derivative convention | `Papers.OrendayLaresRockel2026XiBeta.xi_derivative_formula` | verified | All bivariate copulas; no density assumption. |
| Section 5, proof of Theorem 1: continuity along mixtures | `Papers.OrendayLaresRockel2026XiBeta.xi_mixture_continuous` | verified | Any pair of copulas; proved from the exact quadratic identity. |
| Section 5, proof of Theorem 1: beta stays fixed | `Papers.OrendayLaresRockel2026XiBeta.beta_mixture_fixed` | verified | Both input copulas have the same prescribed beta. |
| Section 5, proof of Theorem 1: intermediate-value step | `Papers.OrendayLaresRockel2026XiBeta.fixed_beta_intermediate` | verified | Supplied copulas with equal beta and xi values bracketing the target; boundary existence remains pending. |
| Proposition 3: two-strip family and coefficient formulas | — | pending | Construct L_b and prove its source CDF and rank coefficients. |
| Proposition 5: sharp inequality and equality case | — | pending | Prove abs(beta)^3<=2 xi and characterize equality. |
| Proposition 6: right boundary | — | pending | Construct the measure-preserving interval exchange for every beta. |
| Theorem 1 as a whole and Section 6 subclasses | — | pending | Combine the missing boundary results with interpolation; formalize subclass constraints. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
