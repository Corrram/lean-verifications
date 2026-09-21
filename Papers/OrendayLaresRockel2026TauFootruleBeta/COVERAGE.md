# Coverage

**Status: complete for stated scope.** Theorem 1.1, Proposition 2.1, Lemma 3.1, Propositions 3.2-3.3, Corollaries 4.1-4.2, the boundary-edge and fibre-symmetry claims, and Section 5's area, unique maximum and volume are checked. This includes arbitrary signed shuffles with zero-width strips, both joint faces, and actual copula attainment of every admissible triple.

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
| Section 3, after Proposition 3.3: centered endpoint formulas | `Papers.OrendayLaresRockel2026TauFootruleBeta.upperTauSeed_coefficients`; `Papers.OrendayLaresRockel2026TauFootruleBeta.centered_tau_endpoints` | verified | The beta=-1 upper seed and its centered images, paired with centered W, provide both tau endpoints at every footrule. The full D_q family is checked separately below. |
| Proposition 2.1: exact tau-footrule region | `Papers.OrendayLaresRockel2026TauFootruleBeta.exact_tau_footrule_region` | verified | Both directions; actual endpoint copulas and a continuous mixture fill each fixed-footrule interval. |
| Corollary 4.2: exact tau-beta projection | `Papers.OrendayLaresRockel2026TauFootruleBeta.tau_beta_bounds`; `Papers.OrendayLaresRockel2026TauFootruleBeta.exact_tau_beta_region` | verified | Direct proof of both sharp quadratic bounds and all intermediate tau values at every beta; does not assume the joint-region theorem. |
| Theorem 1.1: necessary joint inequalities | `Papers.OrendayLaresRockel2026TauFootruleBeta.joint_region_outer_bound` | verified | Every copula triple satisfies all five displayed constraints. |
| Theorem 1.1: simultaneous lower-face attainment | `Papers.OrendayLaresRockel2026TauFootruleBeta.lower_joint_face_attained` | verified | At every admissible (footrule,beta), constructs a copula with those values and tau=4 footrule/3-1/3. Includes beta=1 and every boundary point. |
| Lemma 3.1: general signed shuffle formula | `Papers.OrendayLaresRockel2026TauFootruleBeta.shuffle_tau` | verified | Any finite horizontal/vertical tilings, permutation and diagonal/antidiagonal signs. Constructs an actual copula from the segment laws; includes zero-width strips. The pair sum uses the renamed indices j<i; its sign is +1 exactly when pi(j)<pi(i). |
| Proposition 3.3: full upper seed D_q | `Papers.OrendayLaresRockel2026TauFootruleBeta.upperSeed_coefficients` | verified | The source six-strip family, permutation (3,5,1,6,2,4), and every q in [0,1/4]. Tau=8q^2, footrule=12q^2-1/2, beta=8q-1; actual uniform marginals and both degenerate endpoints. |
| Theorem 1.1: simultaneous upper-face attainment | `Papers.OrendayLaresRockel2026TauFootruleBeta.upper_joint_face_attained` | verified | At every admissible (footrule,beta), an actual centered upper seed attains tau=2 footrule/3+1/3. Includes beta=1 and all boundary points. |
| Theorem 1.1: exact joint region | `Papers.OrendayLaresRockel2026TauFootruleBeta.exact_joint_region` | verified | Both directions for every real triple. The constructed lower and upper endpoints share footrule and beta; the continuous quadratic tau mixture fills the entire fibre. |
| Corollary 4.1: compactness and convexity | `Papers.OrendayLaresRockel2026TauFootruleBeta.jointRegion_closed`; `Papers.OrendayLaresRockel2026TauFootruleBeta.jointRegion_compact`; `Papers.OrendayLaresRockel2026TauFootruleBeta.jointRegion_convex` | verified | Properties of the actual attained subset of real triples, using the proved exact description. |
| Corollary 4.1: exact fixed-footrule rectangles | `Papers.OrendayLaresRockel2026TauFootruleBeta.fixed_footrule_rectangle` | verified | All footrule values in [-1/2,1], including degenerate sections; the source square-root formulas for both beta endpoints. |
| Remark 4.3: fibre symmetry and attained midpoint | `Papers.OrendayLaresRockel2026TauFootruleBeta.fibre_reflection`; `Papers.OrendayLaresRockel2026TauFootruleBeta.fibre_midpoint_attained` | verified | The attained region is invariant under (t,p,b) -> (2p-t,p,b); every admissible (p,b) admits a copula with tau=footrule=p. |
| Section 5: fixed-beta section areas | `Papers.OrendayLaresRockel2026TauFootruleBeta.fixed_beta_section_area`; `Papers.OrendayLaresRockel2026TauFootruleBeta.sectionArea_integral` | verified | Actual two-dimensional Lebesgue section measure equals 3(3-b)^2(1+b)(5-3b)/256 for b in [-1,1], derived by integrating the exact tau fibre. |
| Section 5: unique maximal section | `Papers.OrendayLaresRockel2026TauFootruleBeta.sectionArea_derivative`; `Papers.OrendayLaresRockel2026TauFootruleBeta.sectionArea_maximum`; `Papers.OrendayLaresRockel2026TauFootruleBeta.sectionArea_maximum_attained` | verified | The area derivative, sharp maximum 1/4+sqrt(3)/6, unique maximizer b=1-2/sqrt(3), and attainment, with the beta interval checked. |
| Section 5: volume of the joint region | `Papers.OrendayLaresRockel2026TauFootruleBeta.jointRegion_volume` | verified | Three-dimensional Lebesgue measure of the actual attained region is 31/40. Measure-preserving coordinate reassociation and integration of the checked section areas connect the region to the polynomial integral. |

All previously pending rows are discharged. The scope is the mathematical
statements mapped above in arXiv v1; numerical plots, open problems, and
bibliographic background are not proof claims. The lower seed is represented
by reflected centered ordinal sums; the upper seed uses the source's six
explicit segments. No density restriction, unproved boundary existence, or
coefficient formula is supplied as a hypothesis to the joint-region theorem.

Additional proof modules: [FootruleBetaLower.lean](FootruleBetaLower.lean),
[PairwiseRegions.lean](PairwiseRegions.lean), [LowerJointFace.lean](LowerJointFace.lean),
[ShuffleFormula.lean](ShuffleFormula.lean), [UpperSeed.lean](UpperSeed.lean),
[JointRegion.lean](JointRegion.lean), [JointGeometry.lean](JointGeometry.lean),
and [JointVolume.lean](JointVolume.lean).
