# Coverage

**Status: in progress.** The full explicit xi-rho region (Theorem 1), SI/SD inequality (Theorem 2), and sharp global gap 2/5 (Corollary 1) are verified, with every boundary and equality case. The original diagonal-band family has checked piecewise intercepts, xi/rho coefficients, both explicit inverse branches, parameter ordering, radial symmetry, and all uniform limiting cases. Example 1's PLOD shuffle is checked with xi=1 and rho=13/16. Absolute continuity, density/support and MTP2, the Kendall tau formula, and journal-version comparison remain pending.

## Source and conventions

Source: [arXiv:2506.15897v3](https://arxiv.org/abs/2506.15897v3), 19 May 2026.
Journal reference: [DOI 10.1016/j.jmva.2026.105630](https://doi.org/10.1016/j.jmva.2026.105630); version comparison pending.

Xi conditions coordinate 1 on coordinate 0. Equation (3) is matched to the conditional-CDF definition by the almost-everywhere derivative theorem, without a density assumption. FGM uses the full signed parameter interval [-1,1]. CI and CD in the FGM classification assert conditional monotonicity in both directions, so in particular include the direction used by the source. Within this family the equality case is exactly parameter zero. The general SI/SD inequality and its complete equality classification are proved in StochasticBounds.lean and StochasticEquality.lean. The proof constructs an antitone conditional-CDF version from concavity and compares squared differences with absolute differences. Equality makes almost every conditional CDF either constant or binary; monotonicity in the response threshold excludes mixing the two types at interior thresholds. This is an alternative to the source maximum-principle proof, without a density assumption. The source maximum-principle and extreme-point intermediate assertions are not separately claimed verified.

Lemma 8 is formalized modulo null sets: equality holds exactly when the decreasing function is almost everywhere constant v or the indicator of [0,v]. The source phrases its alternatives pointwise, but changes on null sets cannot affect the integral. Endpoint values and the choice between closed and open cut intervals therefore do not affect our statement. The formal version also includes means v=0 and v=1.

For the vertical boundary, a centered countermonotonic block with identity outside has xi=1 and rho=1-2 alpha^3. Varying alpha over [0,1] realizes the entire rho interval. The interior boundary and its explicit formulas are now proved separately below.

Convexity is proved independently of the curved boundary formulas. A first copula mixture preserves the desired affine coefficient and gives xi no larger than the target convex combination. A second mixture with a proved xi=1 witness at the same coefficient reaches the target xi by continuity. Both steps construct actual copulas, including singular laws and endpoint weights. This also proves attainment of every xi between an existing point and 1 at fixed coefficient; the full explicit region is now established separately below.

## Result map

Proofs are in [SelectedResults.lean](SelectedResults.lean), [RightBoundary.lean](RightBoundary.lean), [StochasticBounds.lean](StochasticBounds.lean), [StochasticEquality.lean](StochasticEquality.lean), [RegionGeometry.lean](RegionGeometry.lean), [DiagonalBandUnit.lean](DiagonalBandUnit.lean), [SharpGap.lean](SharpGap.lean), [SharpSlice.lean](SharpSlice.lean), and [BandOptimization.lean](BandOptimization.lean), imported by
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
| Equations (19)-(22), b=1: actual copula and integral CDF | `Papers.AnsariRockel2026XiRho.unitDiagonalBand_cdf` | verified | The exact piecewise square-root intercept, clamped at 0 and 1. Uniform marginals and nonnegative rectangle increments are proved, including v=0, 1/2, and 1. |
| Proposition 1, b=1: conditional-CDF and derivative correspondence | `Papers.AnsariRockel2026XiRho.unitDiagonalBand_conditionalCDF`; `Papers.AnsariRockel2026XiRho.unitDiagonalBand_derivative` | verified | The actual constructed copula has the source clamped affine first derivative almost everywhere, at every response threshold. |
| Proposition 4(ii), b=1: stochastic increase | `Papers.AnsariRockel2026XiRho.unitDiagonalBand_isSI` | verified | The unit-slope diagonal-band copula is SI; the proof uses its antitone conditional sections. |
| Proposition 5 / Corollary 1: exact coefficient pair | `Papers.AnsariRockel2026XiRho.unitDiagonalBand_xi`; `Papers.AnsariRockel2026XiRho.unitDiagonalBand_rho` | verified | Xi=3/10 and rho=7/10, evaluated from the actual conditional distribution by exact polynomial and square-root integration. |
| Corollary 1: universal sharp gap | `Papers.AnsariRockel2026XiRho.rho_sub_xi_le` | verified | Every bivariate copula, including singular laws, satisfies rho-xi<=2/5. A quadratic projection certificate controls the squared conditional-CDF distance to the optimizer. |
| Corollary 1: unique maximizer and attainment | `Papers.AnsariRockel2026XiRho.rho_sub_xi_eq_iff`; `Papers.AnsariRockel2026XiRho.sharp_gap_attained` | verified | Equality iff C is the constructed unit-slope diagonal-band copula. The theorem supplies an actual attaining copula with the exact coefficient pair. |
| Corollary 1 and reflection: both signs | `Papers.AnsariRockel2026XiRho.abs_rho_sub_xi_le`; `Papers.AnsariRockel2026XiRho.abs_rho_sub_xi_eq_iff` | verified | Absolute rho minus xi is at most 2/5. Equality iff C is the unit-slope maximizing copula or its reflection in coordinate 1. |
| Theorem 1: entire slice at xi=3/10 | `Papers.AnsariRockel2026XiRho.xi_three_tenths_slice`; `Papers.AnsariRockel2026XiRho.xi_three_tenths_rho_max_eq_iff` | verified | Exactly rho in [-7/10,7/10] is attained at xi=3/10, with a unique positive-endpoint copula. Convexity supplies actual interior witnesses. |
| Lemma 5 / Proposition 1: normalization-defined clamped family | `Papers.AnsariRockel2026XiRho.normalizedBand_conditionalCDF` | verified | For every b>=0, construct an actual copula whose conditional CDF is clamp(a_b(v)-b*u,0,1). The intercept is obtained from a proved uniform-mean equation. Identification with the general piecewise intercept in equation (20) is checked below. |
| Proposition 4(ii): SI of the normalized family | `Papers.AnsariRockel2026XiRho.normalizedBand_isSI` | verified | All nonnegative slopes, including the independence endpoint. |
| Theorem 3: sharp support optimization for the normalized family | `Papers.AnsariRockel2026XiRho.normalizedBand_support`; `Papers.AnsariRockel2026XiRho.normalizedBand_support_eq_iff` | verified | For each b>=0, the constructed normalized band uniquely maximizes b*rho-xi over every copula. No supplied optimizer, density assumption, or closed-form coefficient hypothesis. |
| Theorem 3: fixed-xi optimization for the normalized family | `Papers.AnsariRockel2026XiRho.normalizedBand_maximal_rho`; `Papers.AnsariRockel2026XiRho.normalizedBand_maximal_rho_eq_iff` | verified | For b>0, rho is maximal at the constructed band among copulas with xi no larger than its xi, and the maximizer at equal xi is unique. The parameter-to-xi formula and its full-range inversion are checked below. |
| Normalized family: independence and source unit-slope identifications | `Papers.AnsariRockel2026XiRho.normalizedBand_zero`; `Papers.AnsariRockel2026XiRho.normalizedBand_one` | verified | Slope zero is independence; slope one is exactly the explicit copula used in the complete proof of Corollary 1. |
| Equation (7): weighted conditional-CDF and derivative formulas | `Papers.AnsariRockel2026XiRho.rho_conditionalCDF_formula`; `Papers.AnsariRockel2026XiRho.rho_derivative_formula` | verified | Every bivariate copula, including singular laws; rho=12 times the integral of (1-u) times the first conditional CDF or CDF-section derivative, minus 3. |
| Theorem 2: general SI/SD inequality | `Papers.AnsariRockel2026XiRho.si_xi_le_rho`; `Papers.AnsariRockel2026XiRho.sd_xi_le_neg_rho`; `Papers.AnsariRockel2026XiRho.stochastic_xi_le_abs_rho` | verified | For every SI copula xi<=rho, and for every SD copula xi<=-rho; either class satisfies xi<=abs(rho). No family or density restriction. |
| Remark 1(d): obstruction to stochastic monotonicity | `Papers.AnsariRockel2026XiRho.not_stochastically_monotone_of_abs_rho_lt_xi` | verified | If xi>abs(rho), the copula is neither SI nor SD. The separate regression-model interpretation is not formalized. |
| Lemma 8: decreasing-function bound | `Papers.AnsariRockel2026XiRho.lemma8_bound` | verified | Every antitone function into [0,1] with mean v, including v=0 and v=1; its functional is at least v(1-v). |
| Lemma 8: equality modulo null sets | `Papers.AnsariRockel2026XiRho.lemma8_equality` | verified | Equality iff the function is almost everywhere constant v or the indicator of [0,v]. This is the integral-invariant version of the source's pointwise wording; see the convention above. |
| Theorem 2: full equality classification | `Papers.AnsariRockel2026XiRho.si_xi_eq_rho_iff`; `Papers.AnsariRockel2026XiRho.sd_xi_eq_neg_rho_iff`; `Papers.AnsariRockel2026XiRho.stochastic_xi_eq_abs_rho_iff` | verified | Every SI or SD copula, including singular laws: equality in xi<=abs(rho) iff the copula is W, independence, or M. SI equality gives independence or M; SD equality gives independence or W. No family restriction. |
| Theorem 2: strictness away from equality copulas | `Papers.AnsariRockel2026XiRho.stochastic_xi_lt_abs_rho` | verified | Every SI or SD copula other than W, independence, and M has xi<abs(rho). |
| Propositions 2 and 4(iii): remaining family properties | — | pending | Absolute continuity and the explicit density/support, and MTP2. SI, parameter ordering, symmetry, reflection, and all uniform limits are verified. |
| Proposition 5(iii): Kendall tau of the diagonal-band family | — | pending | The general tau formula and its endpoint values, including tau=1/2 at b=1. The exact rho and xi values at b=1 are verified separately. |
| Equations (19)-(20): explicit source normalization | `Papers.AnsariRockel2026XiRho.sourceBandIntercept_mean`; `Papers.AnsariRockel2026XiRho.sourceBand_eq_normalizedBand` | verified | Every b>0, both parameter regimes and all junctions/endpoints; the piecewise square-root intercept constructs the actual normalized optimizer. |
| Equation (19) / Proposition 1: CDF and derivative | `Papers.AnsariRockel2026XiRho.sourceBand_cdf`; `Papers.AnsariRockel2026XiRho.sourceBand_conditionalCDF`; `Papers.AnsariRockel2026XiRho.sourceBand_derivative` | verified | The explicit source copula has the displayed clamped conditional CDF and first derivative almost everywhere, at every response threshold. |
| Proposition 5(i)-(ii): full xi and rho formulas | `Papers.AnsariRockel2026XiRho.sourceBand_xi`; `Papers.AnsariRockel2026XiRho.sourceBand_rho`; `Papers.AnsariRockel2026XiRho.normalizedBand_coefficients` | verified | Exact piecewise coefficients for all b>0, with the independence endpoint b=0 in the normalized family. Evaluated from actual conditional distributions. |
| Equation (5): both explicit inverse branches | `Papers.AnsariRockel2026XiRho.smallXiParameter_inverse`; `Papers.AnsariRockel2026XiRho.largeXiParameter_inverse`; `Papers.AnsariRockel2026XiRho.boundaryParameter_inverse` | verified | Trigonometric inverse for 0<x<=3/10; radical inverse for 3/10<x<1. Each parameter is positive and has exactly xi=x. |
| Theorem 1: all curved boundary points | `Papers.AnsariRockel2026XiRho.boundaryCopula_coefficients`; `Papers.AnsariRockel2026XiRho.sharp_absolute_rho_bound` | verified | The original source family attains every interior positive boundary point, and every copula satisfies the sharp absolute-rho bound. |
| Theorem 1: full explicit region | `Papers.AnsariRockel2026XiRho.exact_region` | verified | An actual copula with coefficients (x,y) exists iff 0<=x<=1 and abs(y)<=M_x, with precisely the source explicit inverse and both endpoints. |
| Theorem 1: unique curved boundary copulas | `Papers.AnsariRockel2026XiRho.upper_boundary_unique`; `Papers.AnsariRockel2026XiRho.lower_boundary_unique` | verified | For every 0<x<1, equality at either boundary identifies the actual source copula or its reflection uniquely. |
| Theorem 3: explicit sharp support value | `Papers.AnsariRockel2026XiRho.explicit_band_support` | verified | All competing copulas and every nonnegative b; the support value uses the evaluated source xi/rho formulas. |
| Remark 3: radial symmetry and negative branch | `Papers.AnsariRockel2026XiRho.normalizedBand_radially_symmetric`; `Papers.AnsariRockel2026XiRho.sourceBand_radially_symmetric`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_cdf`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_coefficients`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_eq_response_reflection` | verified | Every source parameter; reflecting either coordinate gives the same negative-parameter copula. Xi is unchanged and rho changes sign. |
| Proposition 4(i): parameter ordering | `Papers.AnsariRockel2026XiRho.normalizedBand_parameter_order`; `Papers.AnsariRockel2026XiRho.sourceBand_parameter_order`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_parameter_order` | verified | Pointwise lower-orthant order on both branches, including independence in the normalized positive branch. |
| Proposition 3: quantitative uniform estimates | `Papers.AnsariRockel2026XiRho.sourceBand_independence_error`; `Papers.AnsariRockel2026XiRho.sourceBand_comonotonic_error`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_independence_error`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_countermonotonic_error` | verified | CDF error is at most b near independence and 1/b near the corresponding Frechet endpoint, simultaneously at every point. |
| Proposition 3: all uniform limiting cases | `Papers.AnsariRockel2026XiRho.sourceBand_tendstoUniformly_zero`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_tendstoUniformly_zero`; `Papers.AnsariRockel2026XiRho.sourceBand_tendstoUniformly_atTop`; `Papers.AnsariRockel2026XiRho.negativeSourceBand_tendstoUniformly_atTop` | verified | Every positive parameter net tending to zero or infinity, with the negative branch represented by its positive magnitude; limits are independence, M, and W. |
| Example 1: the displayed middle-quarter shuffle | `Papers.AnsariRockel2026XiRho.plodShuffle_cdf`; `Papers.AnsariRockel2026XiRho.plodShuffle_isPQD`; `Papers.AnsariRockel2026XiRho.plodShuffle_xi`; `Papers.AnsariRockel2026XiRho.plodShuffle_rho`; `Papers.AnsariRockel2026XiRho.plod_counterexample` | verified | Four actual increasing strips in order 0,2,1,3; PLOD at every point, xi=1 and rho=13/16. Thus PLOD does not imply xi<=rho. |
| Journal/preprint correspondence | — | pending | Only arXiv v3 is mapped. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.

## Sharp gap and normalized diagonal-band optimization

Corollary 1 is proved independently of the remaining explicit full-region formula.
For a clamped candidate D with section clamp(a(v)-b*u,0,1), the scalar projection
inequality, followed by the shared marginal constraint, gives

$$
6\,d(C,D)^2 \leq \xi(C)-\xi(D)-b\bigl(\rho(C)-\rho(D)\bigr),
$$

where d squared is the integrated squared difference of conditional CDFs.
Its nonnegativity proves global optimality; its zero characterization proves
uniqueness of the copula itself. Every competing copula is included, without
an absolute-continuity or SI hypothesis.

At b=1 the explicit intercept is sqrt(2v) below v=1/2 and
2-sqrt(2(1-v)) above. Exact integration proves xi=3/10 and rho=7/10,
so the maximum gap is 2/5. This finishes Corollary 1. Theorem 1 is now also proved in full by the general formulas and inverse below.
The exact xi=3/10 slice also follows by reflection and the already verified
convexity theorem.

For general b>=0 the intercept is selected from the proved equation
integral clamp(a-b*u,0,1) du=v. The explicit piecewise intercept in equation
(20) is proved to satisfy this same equation; support uniqueness identifies
the constructed source copula with the normalized optimizer. Exact integration
gives both branches of Proposition 5's xi and rho formulas. The trigonometric
and radical expressions in equation (5) invert xi on its full interior range.
The sharp support bound and convexity then prove every inclusion and witness
in the exact region, with uniqueness of both curved boundary copulas.

Parameter ordering follows from equal means and ordered slopes of clamped
sections. Radial symmetry follows from uniqueness of the support optimizer.
Uniform convergence is quantitative: CDF errors are bounded by b at
independence and by 1/b at M or W. These results do not assume a density.
Absolute continuity, explicit density/support, MTP2, and Kendall tau remain
separate proof obligations.
