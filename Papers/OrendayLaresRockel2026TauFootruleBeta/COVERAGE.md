# Coverage

**Status: in progress.** Biaffinity, fixed-fibre interpolation, equation (9), and the sharp upper footrule-beta bound with attainment are checked. The lower footrule-beta bound, tau-footrule bounds, simultaneous boundary shuffles, and full joint region remain pending.

## Source and conventions

Source: [arXiv:2607.12841v1](https://arxiv.org/abs/2607.12841v1), 14 July 2026.

Tau=4 integral C dC-1, footrule=6 integral C(t,t) dt-2, and beta=4 C(1/2,1/2)-1. The library writes Q(C,D)=4 integral C dD-1; symmetry of Q matches the argument order of equation (6). The two endpoint copulas in the interpolation theorem must already have the same footrule and beta. Pairwise bounds alone are not treated as joint attainability. Tau along a mixture is quadratic, not affine.

The upper footrule-beta boundary is proved by comparing diagonals and integrating. Its centered W witness is an alternative attaining copula; this result does not supply the simultaneous tau extrema required for the joint region.

## Result map

Proofs are in [Mixtures.lean](Mixtures.lean), [CenteredOrdinal.lean](CenteredOrdinal.lean), and [FootruleBeta.lean](FootruleBeta.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Section 2, equation (6): biaffinity of Q | `Papers.OrendayLaresRockel2026TauFootruleBeta.concordance_mixture` | verified | Any four copulas and two closed-interval mixture weights; source argument order agrees by Q symmetry. |
| Section 4, proof of Theorem 1.1: continuity of tau | `Papers.OrendayLaresRockel2026TauFootruleBeta.tau_mixture_continuous` | verified | Any pair of copulas, including singular ones. |
| Section 4, proof of Theorem 1.1: fill a vertical fibre | `Papers.OrendayLaresRockel2026TauFootruleBeta.fixed_footrule_beta_intermediate` | verified | Supplied copulas share both footrule and beta and bracket the requested tau. No boundary existence is assumed implicitly. |
| Equation (9): construction and central-square CDF | `Papers.OrendayLaresRockel2026TauFootruleBeta.centeredOrdinal_cdf` | verified | Parameter alpha is the central width 1-2a; the central CDF is a+alpha C, including alpha=0. |
| Equation (9): degenerate and full-width endpoints | `Papers.OrendayLaresRockel2026TauFootruleBeta.centeredOrdinal_zero`; `Papers.OrendayLaresRockel2026TauFootruleBeta.centeredOrdinal_one` | verified | Width zero gives M; width one recovers the supplied copula. |
| Equation (9): tau, footrule and beta transformations | `Papers.OrendayLaresRockel2026TauFootruleBeta.centeredOrdinal_tau`; `Papers.OrendayLaresRockel2026TauFootruleBeta.centeredOrdinal_footrule`; `Papers.OrendayLaresRockel2026TauFootruleBeta.centeredOrdinal_beta` | verified | Tau and footrule transform with alpha squared; beta transforms with alpha. No density assumption. |
| Proposition 2.1, upper inequality in (8): diagonal comparison | `Papers.OrendayLaresRockel2026TauFootruleBeta.diagonal_le_centralW` | verified | At fixed beta, every diagonal is pointwise bounded above by a centered W block. |
| Proposition 2.1, upper inequality in (8): attaining family | `Papers.OrendayLaresRockel2026TauFootruleBeta.footruleBetaUpper_beta`; `Papers.OrendayLaresRockel2026TauFootruleBeta.footruleBetaUpper_footrule` | verified | Every b in [-1,1]; the centered W witness has beta=b and footrule=1-3(1-b)^2/8, including both endpoints. |
| Proposition 2.1, upper inequality in (8): universal sharp bound | `Papers.OrendayLaresRockel2026TauFootruleBeta.footrule_le_beta_upper`; `Papers.OrendayLaresRockel2026TauFootruleBeta.maximal_footrule_at_beta` | verified | All copulas, including singular ones. The maximum at each beta is attained; no uniqueness claim. |
| Proposition 2.1 beyond the upper bound in (8) | — | pending | The lower footrule-beta bound and the tau-footrule bounds, with attainment. |
| Lemma 3.1 and Section 3 shuffle families | — | pending | General shuffle tau formula and simultaneous boundary coefficient values. |
| Theorem 1.1 as a whole | — | pending | Construct the simultaneous endpoints and prove all region inequalities. |
| Corollaries 4.1-4.2 and Section 5 | — | pending | Joint-region geometry, projection and volume. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
