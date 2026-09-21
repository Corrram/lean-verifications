# Coverage

**Status: in progress.** The derivative conventions, endpoints, entire xi=1 boundary, convexity of the full region, and attainment from any existing point up to xi=1 at fixed rho are checked. The full SI/SD Theorem 2 with all equality cases and Lemma 8 modulo null sets are verified. The curved diagonal-band boundary, full explicit region, and sharp global gap remain pending.

## Source and conventions

Source: [arXiv:2506.15897v3](https://arxiv.org/abs/2506.15897v3), 19 May 2026.
Journal reference: [DOI 10.1016/j.jmva.2026.105630](https://doi.org/10.1016/j.jmva.2026.105630); version comparison pending.

Xi conditions coordinate 1 on coordinate 0. Equation (3) is matched to the conditional-CDF definition by the almost-everywhere derivative theorem, without a density assumption. FGM uses the full signed parameter interval [-1,1]. CI and CD in the FGM classification assert conditional monotonicity in both directions, so in particular include the direction used by the source. Within this family the equality case is exactly parameter zero. The general SI/SD inequality and its complete equality classification are proved in StochasticBounds.lean and StochasticEquality.lean. The proof constructs an antitone conditional-CDF version from concavity and compares squared differences with absolute differences. Equality makes almost every conditional CDF either constant or binary; monotonicity in the response threshold excludes mixing the two types at interior thresholds. This is an alternative to the source maximum-principle proof, without a density assumption. The source maximum-principle and extreme-point intermediate assertions are not separately claimed verified.

Lemma 8 is formalized modulo null sets: equality holds exactly when the decreasing function is almost everywhere constant v or the indicator of [0,v]. The source phrases its alternatives pointwise, but changes on null sets cannot affect the integral. Endpoint values and the choice between closed and open cut intervals therefore do not affect our statement. The formal version also includes means v=0 and v=1.

For the vertical boundary, a centered countermonotonic block with identity outside has xi=1 and rho=1-2 alpha^3. Varying alpha over [0,1] realizes the entire rho interval. This does not assert the source's diagonal-band formulas for 0<xi<1.

Convexity is proved independently of the curved boundary formulas. A first copula mixture preserves the desired affine coefficient and gives xi no larger than the target convex combination. A second mixture with a proved xi=1 witness at the same coefficient reaches the target xi by continuity. Both steps construct actual copulas, including singular laws and endpoint weights. This also proves attainment of every xi between an existing point and 1 at fixed coefficient; it does not assert that the infimum of a slice is attained or that the full region is closed.

## Result map

Proofs are in [SelectedResults.lean](SelectedResults.lean), [RightBoundary.lean](RightBoundary.lean), [StochasticBounds.lean](StochasticBounds.lean), [StochasticEquality.lean](StochasticEquality.lean), and [RegionGeometry.lean](RegionGeometry.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (3): derivative convention | `Papers.AnsariRockel2026XiRho.xi_derivative_formula` | verified | All bivariate copulas; constant extension of CDF sections outside [0,1]; endpoints have zero measure. |
| Theorem 1: xi=0 endpoint | `Papers.AnsariRockel2026XiRho.xi_zero_slice` | verified | Xi=0 characterizes independence and hence rho=0; no interior boundary is claimed. |
| Theorem 1: rho=+1 or -1 endpoints | `Papers.AnsariRockel2026XiRho.rho_extreme_implies_xi_one` | verified | All bivariate copulas; extremal rho implies xi=1. |
| Theorem 2: FGM subclass correspondence | `Papers.AnsariRockel2026XiRho.fgm_stochastically_monotone` | verified | Every FGM copula with abs(theta)<=1 is CI or CD. |
| Theorem 2: inequality restricted to FGM | `Papers.AnsariRockel2026XiRho.fgm_xi_le_abs_rho` | verified | Only the signed FGM family, including both parameter endpoints. |
| Theorem 2: equality restricted to FGM | `Papers.AnsariRockel2026XiRho.fgm_xi_eq_abs_rho_iff` | verified | Within FGM, xi=abs(rho) iff theta=0. The unrestricted SI/SD equality characterization is checked below. |
| Theorem 1: entire vertical boundary at xi=1 | `Papers.AnsariRockel2026XiRho.xi_one_slice`; `Papers.AnsariRockel2026XiRho.symmetric_xi_one_attained` | verified | Every rho in [-1,1] is attained with xi=1, even by a radially symmetric copula. Constructed centered W blocks and a proved continuous rho path supply all witnesses. |
| Theorem 1: attainment up to xi=1 at fixed rho | `Papers.AnsariRockel2026XiRho.fixed_coefficient_upward` | verified | Every attained (x,y) extends to all (z,y) with x<=z<=1. Uses an actual xi=1 witness at the same coefficient and a continuous copula-mixture path. |
| Theorem 1: convexity of the entire attainable region | `Papers.AnsariRockel2026XiRho.attainable_region_convex` | verified | Every convex combination of attainable pairs is attained. Independent two-mixture proof; no assumed curved-boundary formula or full-region characterization. |
| Theorem 1: curved boundary and interior region | — | pending | Construct the diagonal-band family, prove its coefficient formulas, global bounds, uniqueness and the full explicit region. The entire xi=1 slice, convexity, and fixed-rho upward attainment are checked above. |
| Corollary 1: sharp global gap 0.4 | — | pending | Prove the universal bound and unique maximizer. |
| Equation (7): weighted conditional-CDF and derivative formulas | `Papers.AnsariRockel2026XiRho.rho_conditionalCDF_formula`; `Papers.AnsariRockel2026XiRho.rho_derivative_formula` | verified | Every bivariate copula, including singular laws; rho=12 times the integral of (1-u) times the first conditional CDF or CDF-section derivative, minus 3. |
| Theorem 2: general SI/SD inequality | `Papers.AnsariRockel2026XiRho.si_xi_le_rho`; `Papers.AnsariRockel2026XiRho.sd_xi_le_neg_rho`; `Papers.AnsariRockel2026XiRho.stochastic_xi_le_abs_rho` | verified | For every SI copula xi<=rho, and for every SD copula xi<=-rho; either class satisfies xi<=abs(rho). No family or density restriction. |
| Remark 1(d): obstruction to stochastic monotonicity | `Papers.AnsariRockel2026XiRho.not_stochastically_monotone_of_abs_rho_lt_xi` | verified | If xi>abs(rho), the copula is neither SI nor SD. The separate regression-model interpretation is not formalized. |
| Lemma 8: decreasing-function bound | `Papers.AnsariRockel2026XiRho.lemma8_bound` | verified | Every antitone function into [0,1] with mean v, including v=0 and v=1; its functional is at least v(1-v). |
| Lemma 8: equality modulo null sets | `Papers.AnsariRockel2026XiRho.lemma8_equality` | verified | Equality iff the function is almost everywhere constant v or the indicator of [0,v]. This is the integral-invariant version of the source's pointwise wording; see the convention above. |
| Theorem 2: full equality classification | `Papers.AnsariRockel2026XiRho.si_xi_eq_rho_iff`; `Papers.AnsariRockel2026XiRho.sd_xi_eq_neg_rho_iff`; `Papers.AnsariRockel2026XiRho.stochastic_xi_eq_abs_rho_iff` | verified | Every SI or SD copula, including singular laws: equality in xi<=abs(rho) iff the copula is W, independence, or M. SI equality gives independence or M; SD equality gives independence or W. No family restriction. |
| Theorem 2: strictness away from equality copulas | `Papers.AnsariRockel2026XiRho.stochastic_xi_lt_abs_rho` | verified | Every SI or SD copula other than W, independence, and M has xi<abs(rho). |
| Journal/preprint correspondence | — | pending | Only arXiv v3 is mapped. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
