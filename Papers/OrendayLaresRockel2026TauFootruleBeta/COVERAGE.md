# Coverage

**Status: in progress.** All three pairwise regions, all necessary joint inequalities and the entire lower tau face are checked, with actual attaining copulas. The general shuffle formula, upper tau face, remaining joint attainment and joint-region geometry remain pending.

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
| Proposition 2.1, lower inequality in (8) | `Papers.OrendayLaresRockel2026TauFootruleBeta.diagonal_beta_lower`; `Papers.OrendayLaresRockel2026TauFootruleBeta.beta_lower_le_footrule` | verified | Pointwise diagonal comparison gives footrule>=3(1+beta)^2/16-1/2 for every copula. |
| Proposition 3.2: lower-boundary coefficient values | `Papers.OrendayLaresRockel2026TauFootruleBeta.lowerSeed_coefficients`; `Papers.OrendayLaresRockel2026TauFootruleBeta.footruleBetaLower_coefficients` | verified | Constructed reflected centered ordinal sum; alpha=2r. Tau=(1+b)^2/4-1, footrule=3(1+b)^2/16-1/2, beta=b. No general shuffle formula is assumed. |
| Proposition 2.1: sharp lower footrule-beta bound | `Papers.OrendayLaresRockel2026TauFootruleBeta.minimal_footrule_at_beta` | verified | The minimum at every b in [-1,1] is attained. |
| Proposition 2.1: exact footrule-beta region | `Papers.OrendayLaresRockel2026TauFootruleBeta.exact_footrule_beta_region` | verified | Both directions and every boundary case; actual copulas attain all intermediate pairs. |
| Proposition 2.1: tau-footrule bounds | `Papers.OrendayLaresRockel2026TauFootruleBeta.tau_footrule_bounds` | verified | Both universal linear inequalities, including singular copulas. |
| Section 3, after Proposition 3.3: centered endpoint formulas | `Papers.OrendayLaresRockel2026TauFootruleBeta.upperTauSeed_coefficients`; `Papers.OrendayLaresRockel2026TauFootruleBeta.centered_tau_endpoints` | verified | The beta=-1 upper seed and its centered images, paired with centered W, provide both tau endpoints at every footrule. This does not identify the full D_q family. |
| Proposition 2.1: exact tau-footrule region | `Papers.OrendayLaresRockel2026TauFootruleBeta.exact_tau_footrule_region` | verified | Both directions; actual endpoint copulas and a continuous mixture fill each fixed-footrule interval. |
| Corollary 4.2: exact tau-beta projection | `Papers.OrendayLaresRockel2026TauFootruleBeta.tau_beta_bounds`; `Papers.OrendayLaresRockel2026TauFootruleBeta.exact_tau_beta_region` | verified | Direct proof of both sharp quadratic bounds and all intermediate tau values at every beta; does not assume the joint-region theorem. |
| Theorem 1.1: necessary joint inequalities | `Papers.OrendayLaresRockel2026TauFootruleBeta.joint_region_outer_bound` | verified | Every copula triple satisfies all five displayed constraints. |
| Theorem 1.1: simultaneous lower-face attainment | `Papers.OrendayLaresRockel2026TauFootruleBeta.lower_joint_face_attained` | verified | At every admissible (footrule,beta), constructs a copula with those values and tau=4 footrule/3-1/3. Includes beta=1 and every boundary point. |
| Lemma 3.1 and Proposition 3.3 | — | pending | General shuffle tau formula and the full upper seed D_q with simultaneous coefficient values. |
| Theorem 1.1: upper face and remaining joint attainment | — | pending | Construct the upper tau endpoint for every admissible (footrule,beta), then apply the checked fixed-fibre interpolation. The lower face and necessity are proved above. |
| Corollary 4.1 and Section 5 | — | pending | Joint-region geometry, volume and section maxima. Corollary 4.2 is proved directly above. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.

Additional proof modules: [FootruleBetaLower.lean](FootruleBetaLower.lean), [PairwiseRegions.lean](PairwiseRegions.lean), [LowerJointFace.lean](LowerJointFace.lean).
