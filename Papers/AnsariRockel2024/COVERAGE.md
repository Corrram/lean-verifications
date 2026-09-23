# Coverage

**Status: in progress.** Selected Tables 1-6 results are checked: both Clayton CDF branches, special and limiting cases, and exact signed Clayton CI/CD classification, quadrant dependence, CDF-level TP2 classification, and both tail coefficients; FGM, Frechet and Mardia association formulas and tails; FGM conditional monotonicity, lower orthant order and its actual density with TP2 classification; Nelsen 7 CDF, endpoints, CD, parameter order and both tail limits. Both tail limits for Gumbel, Marshall-Olkin, Cuadras-Auge and Tawn, the exact FGM Schur order, and the corrected Frechet parameter order are also checked. The exact Frechet and Mardia CI/CD and absolute-continuity/density-TP2 classifications, and an incomparable Mardia pair, are checked as well. Nelsen 7 now also has its exact conditional CDF, xi=1-theta formula, CI region and Schur parameter order checked. Lemmas 2.6 and 2.8 (both directions on the monotone classes) and Proposition 3.2 are fully checked, as are copula-level concordance and xi consistency and both tail-order implications. Theorem 3.4(i)-(ii) is checked from max-stability, and each directional Schur equivalence and both xi consequences are checked under an explicit CI hypothesis; ordered extreme-value rho, tau and tail limits are also checked; Marshall-Olkin and Cuadras-Auge CI, lower orthant and both-direction Schur parameter orders are checked on the full interval. Cuadras-Auge also has its actual conditional CDF and all three exact Table 6 formulas (rho, xi, tau) checked; Marshall-Olkin has its actual conditional CDF and full two-parameter rho, xi and tau formulas checked. Exact density-TP2 and absolute-continuity classifications are checked for both common-shock families. Other family entries, remaining general order correspondences and journal comparison remain pending.

## Source and conventions

Source: [arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3).
Correspondence with the [journal version](https://doi.org/10.1515/demo-2024-0002)
remains pending.

A copula is represented by its probability measure. The classical
representation theorem below proves existence and uniqueness from the
classical boundary and rectangle conditions. The FGM CDF is checked explicitly.
Fréchet uses weights $a$ on $M$, $b$ on $W$, and $1-a-b$ on independence,
with $a,b\geq0$ and $a+b\leq1$. Mardia uses
$a=\theta^2(1+\theta)/2$ and $b=\theta^2(1-\theta)/2$.
Signed parameters satisfy $-1\leq\theta\leq1$; singular endpoints are included.
CI and CD mean conditional monotonicity in both directions. Rho and tau
use the source population normalizations; xi is coordinate 1 given coordinate 0.

The library defines xi using a regular conditional CDF. The bridge to the
source's almost-everywhere partial derivative is proved in
[ConditionalDerivative.lean](https://github.com/Corrram/copula/blob/765dfec9bdd19c41414738718e818f25e2fe825f/Copula/Rank/ConditionalDerivative.lean),
without assuming an absolutely continuous copula.

The additional extreme-value tails use actual copula constructors and the
power-diagonal limit proofs in the pinned library. The parameters are finite:
Gumbel and Tawn have theta>=1; Marshall-Olkin, Cuadras-Auge and Tawn weights
include their closed unit intervals. The lower tail at M is treated separately.
These tail results do not establish the families' remaining dependence or
association-coefficient table cells.

## Result map

Every row refers to arXiv v3. Each named declaration is compiled, printed,
and checked against the standard axiom allowlist in [Axioms.lean](Axioms.lean).

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Section 2.1: classical representation | `Papers.AnsariRockel2024.classical_representation` | verified | Bivariate classical boundary and rectangle conditions; unique representing measure. |
| Table 5: FGM CDF | `Papers.AnsariRockel2024.fgm_cdf` | verified | Entire closed square and signed parameter interval. |
| Tables 1–2: Clayton CDF, both parameter branches | `Papers.AnsariRockel2024.clayton_positive_cdf`; `Papers.AnsariRockel2024.clayton_negative_cdf`; `Papers.AnsariRockel2024.clayton_positive_zero_axes`; `Papers.AnsariRockel2024.clayton_negative_zero_axes` | verified | The source formula is checked for every positive θ and every negative θ in [-1,0), throughout the closed square. The negative branch explicitly truncates the base before exponentiation; zero-coordinate CDF values are handled separately, avoiding undefined negative powers of zero. |
| Table 2: Clayton special and limiting cases | `Papers.AnsariRockel2024.clayton_negative_one`; `Papers.AnsariRockel2024.clayton_tendsto_zero`; `Papers.AnsariRockel2024.clayton_tendsto_atTop` | verified | At θ=-1 the copula equals W. Positive θ tending to zero gives the independence CDF, and θ tending to infinity gives M, at every point of the closed square. These are pointwise CDF limits, not a claim of uniform convergence or rank-coefficient convergence. |
| Table 2: Clayton θ=1 rational case | `Papers.AnsariRockel2024.clayton_one_cdf` | verified | On positive coordinates the CDF equals uv/(u+v-uv), with a proved positive denominator. Zero-coordinate values are covered by the separate axis theorem; the undefined 0/0 expression is not used. |
| Table 3: positive Clayton CI/CD region | `Papers.AnsariRockel2024.clayton_positive_ci`; `Papers.AnsariRockel2024.clayton_positive_not_cd` | verified | Every θ>0 is CI and not CD. CDF-section concavity and Archimedean symmetry prove CI; a strict midpoint comparison with independence excludes CD. Density TP2 remains open. |
| Table 3: positive Clayton quadrant dependence | `Papers.AnsariRockel2024.clayton_positive_pqd` | verified | Every θ>0 has C(u,v)≥uv on the closed square. This follows from the now verified CI entry; density TP2 remains open. The proof lives in the pinned copula package. |
| Table 3: Clayton parameter endpoints | `Papers.AnsariRockel2024.clayton_zero_ci_cd`; `Papers.AnsariRockel2024.clayton_negative_one_cd` | verified | At θ=0 the independence copula is both CI and CD. At θ=−1 the negative Clayton copula equals W and is CD. The full negative interval is verified in the next row. |
| Table 3: negative Clayton CI/CD region | `Papers.AnsariRockel2024.clayton_negative_cd`; `Papers.AnsariRockel2024.clayton_negative_not_ci` | verified | Every θ in [−1,0) is CD and not CI. CDF-section convexity across the truncation boundary and Archimedean symmetry prove CD; a strict midpoint comparison with independence excludes CI. Density TP2 remains open. |
| Table 3: negative Clayton quadrant dependence | `Papers.AnsariRockel2024.clayton_negative_nqd` | verified | Every θ in [-1,0) has C(u,v)≤uv on the closed square, including W at θ=-1. This follows from the now verified CD entry. The proof lives in the pinned copula package. |
| Additional Clayton CDF total-positivity classification | `Papers.AnsariRockel2024.clayton_positive_cdf_tp2`; `Papers.AnsariRockel2024.clayton_zero_cdf_tp2`; `Papers.AnsariRockel2024.clayton_negative_not_cdf_tp2` | verified | The CDF is TP2 for θ≥0 and fails TP2 for −1≤θ<0, including the W endpoint. This is a separate CDF property; the Table 3 density-TP2 claim remains pending. |
| Table 3: Clayton θ=−1 density TP2 exclusion | `Papers.AnsariRockel2024.clayton_negative_one_not_density_tp2` | verified | At θ=−1 the copula is W, which is singular and has no Lebesgue MTP2 density. The interior negative and positive density-TP2 parameter ranges remain pending. |
| Table 3: positive Clayton analytic density candidate | `Papers.AnsariRockel2024.clayton_cdf_positive_eq_analytic`; `Papers.AnsariRockel2024.clayton_cdf_formula_hasDerivAt_first`; `Papers.AnsariRockel2024.clayton_cdf_formula_hasDerivAt_second`; `Papers.AnsariRockel2024.clayton_mixed_derivative_eq_densityFormula` | verified | On strictly positive unit coordinates, the actual Clayton CDF equals its analytic formula, and the formula’s first and mixed derivatives are evaluated. The mixed derivative is exactly the pinned package’s nonnegative MTP2 candidate. This is pointwise calculus; integration to the actual copula measure remains pending. |
| Table 3: positive Clayton density on positive rectangles | `Papers.AnsariRockel2024.clayton_density_formula_integral_second`; `Papers.AnsariRockel2024.clayton_cdf_formula_integral_first`; `Papers.AnsariRockel2024.clayton_density_formula_positive_rectangle`; `Papers.AnsariRockel2024.clayton_density_formula_positive_rectangle_eq_measure`; `Papers.AnsariRockel2024.clayton_densityFormula_positive_rectangle_eq_measure`; `Papers.AnsariRockel2024.clayton_withDensity_positive_rectangle_eq_measure`; `Papers.AnsariRockel2024.clayton_density_formula_cutoff_square`; `Papers.AnsariRockel2024.clayton_density_formula_cutoff_square_bounds`; `Papers.AnsariRockel2024.clayton_density_formula_cutoff_square_tendsto_one`; `Papers.AnsariRockel2024.clayton_density_formula_positive_rectangle_cdf_bounds`; `Papers.AnsariRockel2024.clayton_density_formula_cutoff_rectangle_tendsto_cdf` | verified | The pinned package density candidate itself integrates over every positive half-open unit-square rectangle to the actual copula mass, and its `withDensity` measure agrees there; the matching analytic real-coordinate integral equals the four-corner CDF increment. The one-coordinate FTC identities and cutoff-square bounds are also checked; its integral lies between 1−2r and 1−r, hence tends to one as the positive cutoff vanishes. More generally, a rectangle with equal vanishing lower cutoffs has candidate-density integral tending to its upper-corner Clayton CDF. Conversion to a global density on the unit square remains pending. |
| Table 3: positive Clayton density TP2 | — | pending | The pinned copula package proves that the standard candidate formula is measurable, nonnegative, and MTP2. Its pointwise identification as the mixed derivative and its actual unit-square rectangle mass equality away from the axes are proved. Global integrability and extension of the positive-rectangle measure equality across the coordinate axes remain pending, so `HasMTP2Density` is not claimed. |
| Table 3: positive Clayton tail pair | `Papers.AnsariRockel2024.clayton_positive_lower_tail`; `Papers.AnsariRockel2024.clayton_positive_upper_tail` | verified | For every θ>0, (λL,λU)=(2^(−1/θ),0). The lower coefficient follows from the exact diagonal ratio; the upper coefficient follows from the diagonal derivative at one. |
| Table 3: negative Clayton tail pair | `Papers.AnsariRockel2024.clayton_negative_lower_tail`; `Papers.AnsariRockel2024.clayton_negative_upper_tail` | verified | For every θ in [−1,0), both coefficients are zero. A general package theorem proves NQD forces zero lower and upper tail coefficients. The θ=0 independence case is already covered by the package. |
| Section 2.4: derivative formula for xi | `Papers.AnsariRockel2024.xi_derivative_formula` | verified | All bivariate copulas; almost-everywhere correspondence with the conditional CDF. |
| Table 6, FGM, Spearman rho | `Papers.AnsariRockel2024.fgm_rho` | verified | Full signed interval, including zero and both endpoints. |
| Table 6, FGM, Kendall tau | `Papers.AnsariRockel2024.fgm_tau` | verified | Full signed interval, including zero and both endpoints. |
| Table 6, FGM, Chatterjee xi | `Papers.AnsariRockel2024.fgm_xi` | verified | Full signed interval, including zero and both endpoints. |
| Table 6, Frechet, Spearman rho | `Papers.AnsariRockel2024.frechet_rho` | verified | Full weight simplex, including singular endpoints. |
| Table 6, Frechet, Kendall tau | `Papers.AnsariRockel2024.frechet_tau` | verified | Full weight simplex, including singular endpoints. |
| Table 6, Frechet, Chatterjee xi | `Papers.AnsariRockel2024.frechet_xi` | verified | Full weight simplex, including singular endpoints. |
| Table 6, Mardia, Spearman rho | `Papers.AnsariRockel2024.mardia_rho` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Table 6, Mardia, Kendall tau | `Papers.AnsariRockel2024.mardia_tau` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Table 6, Mardia, Chatterjee xi | `Papers.AnsariRockel2024.mardia_xi` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Table 5 / Appendix A.4.1: FGM CI | `Papers.AnsariRockel2024.fgm_ci` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.1: FGM CD | `Papers.AnsariRockel2024.fgm_cd` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.2: FGM lower orthant order | `Papers.AnsariRockel2024.fgm_lowerOrthant` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.3: FGM lower and upper tails | `Papers.AnsariRockel2024.fgm_tails` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.3: Frechet tails | `Papers.AnsariRockel2024.frechet_tails` | verified | Full weight simplex, including singular endpoints. |
| Table 5 / Appendix A.4.3: Mardia tails | `Papers.AnsariRockel2024.mardia_tails` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Table 5 / Appendix A.4.1: FGM density | `Papers.AnsariRockel2024.fgm_density` | verified | Actual copula measure equals Lebesgue measure with the displayed continuous density; all signed parameters. |
| Table 5 / Appendix A.4.1: FGM density TP2 | `Papers.AnsariRockel2024.fgm_density_tp2_iff`; `Papers.AnsariRockel2024.fgm_has_tp2_density` | verified | The displayed density is TP2 iff theta>=0; for nonnegative theta it supplies a HasMTP2Density witness. No claim about TP2 of the CDF is substituted for density TP2. |
| Tables 1-2: Nelsen 7 CDF and endpoints | `Papers.AnsariRockel2024.nelsen7_cdf`; `Papers.AnsariRockel2024.nelsen7_endpoints` | verified | Entire square and theta in [0,1], including W at zero and independence at one. |
| Table 3 / Appendix A.1.1: Nelsen 7 CD | `Papers.AnsariRockel2024.nelsen7_cd` | verified | Conditional decreasingness in both directions for every theta in [0,1]. |
| Table 3 / Appendix A.1.2: Nelsen 7 lower orthant order | `Papers.AnsariRockel2024.nelsen7_lowerOrthant_iff` | verified | Comparison holds iff the parameters are ordered; full closed parameter interval. |
| Table 3: Nelsen 7 tail dependence | `Papers.AnsariRockel2024.nelsen7_tails` | verified | Both limits exist and equal zero, including both parameter endpoints. |
| Table 3 / Appendix A.1.3: Gumbel-Hougaard tails | `Papers.AnsariRockel2024.gumbel_tails` | verified | Both limits exist for every finite theta>=1: lower=0, upper=2-2^(1/theta). Includes theta=1. |
| Table 5 / Appendix A.2.3: Marshall-Olkin tails | `Papers.AnsariRockel2024.marshallOlkin_tails` | verified | Both limits for all alpha,beta in [0,1]: upper=min(alpha,beta), lower=1 exactly at alpha=beta=1, otherwise 0. Singular and zero-weight parameters included. |
| Table 5 / Appendix A.2.3: Cuadras-Auge tails | `Papers.AnsariRockel2024.cuadrasAuge_tails` | verified | Both limits for every delta in [0,1]: upper=delta; lower=1 at delta=1 (M), otherwise 0. |
| Table 5 / Appendix A.2.3: Tawn tails | `Papers.AnsariRockel2024.tawn_tails` | verified | Both limits for finite theta>=1 and alpha,beta in [0,1]: lower=0, upper=alpha+beta-(alpha^theta+beta^theta)^(1/theta). All zero weights and theta=1 included; no infinite-parameter substitution. |
| Table 5 / Appendix A.4.2: exact FGM Schur order | `Papers.AnsariRockel2024.fgm_schur_iff` | verified | Schur comparison in both directions iff abs(theta)<=abs(eta), on the full signed parameter interval [-1,1]. The order uses the continuous convex-test characterization of conditional-CDF majorization. |
| Table 5 / Appendix A.4.2: corrected Frechet parameter order | `Papers.AnsariRockel2024.frechet_parameter_order` | verified | On the full valid weight simplex, increasing the M weight and decreasing the W weight increases the copula in lower orthant order. This corrects the printed direction for the W weight; no characterization of all comparable weight pairs is claimed. |
| Table 5 / Appendix A.4.2: counterexample to printed Frechet order | `Papers.AnsariRockel2024.frechet_order_counterexample` | verified | At fixed M weight zero, raising W's weight from zero to one gives independence then W; independence is not below W in lower orthant order. |
| Table 5 / Appendix A.4.1: Frechet CI | `Papers.AnsariRockel2024.frechet_ci_iff` | verified | Full valid weight simplex: CI iff the W weight b is zero; both conditioning directions and all endpoints. |
| Table 5 / Appendix A.4.1: Frechet CD | `Papers.AnsariRockel2024.frechet_cd_iff` | verified | Full valid weight simplex: CD iff the M weight a is zero; both conditioning directions and all endpoints. |
| Support for the density-TP2 correction: Frechet absolute continuity | `Papers.AnsariRockel2024.frechet_absolutelyContinuous_iff` | verified | The actual copula measure is absolutely continuous with respect to square Lebesgue measure iff a=b=0. Positive M or W weight charges a Lebesgue-null diagonal. |
| Correction to Table 5 / Appendix A.4.1: Frechet density TP2 | `Papers.AnsariRockel2024.frechet_density_tp2_iff` | verified | Under the literal Lebesgue-density definition, HasMTP2Density iff a=b=0 (independence). The singular M endpoint has no Lebesgue density. |
| Correction to Table 5 / Appendix A.4.1: Mardia CI | `Papers.AnsariRockel2024.mardia_ci_iff` | verified | Full signed interval [-1,1]: CI iff theta=0 or theta=1. Includes the independence case omitted in the printed classification. |
| Correction to Table 5 / Appendix A.4.1: Mardia CD | `Papers.AnsariRockel2024.mardia_cd_iff` | verified | Full signed interval [-1,1]: CD iff theta=0 or theta=-1. Includes the independence case omitted in the printed classification. |
| Support for the density-TP2 correction: Mardia absolute continuity | `Papers.AnsariRockel2024.mardia_absolutelyContinuous_iff` | verified | Full signed interval: the actual copula measure is absolutely continuous with respect to square Lebesgue measure iff theta=0. |
| Correction to Table 5 / Appendix A.4.1: Mardia density TP2 | `Papers.AnsariRockel2024.mardia_density_tp2_iff` | verified | Full signed interval: HasMTP2Density iff theta=0 (independence), with the valid nonnegative W weight. |
| Table 5 / Appendix A.4.2: Mardia lack of parameter ordering | `Papers.AnsariRockel2024.mardia_not_lowerOrthant_ordered` | verified | The copulas at theta=0 and theta=1/2 are incomparable in lower orthant order. Explicit CDF witnesses at (1/8,1/8) and (1/8,7/8) rule out the two directions. |
| Table 6 / Appendix A.5.1: Nelsen 7 conditional CDF | `Papers.AnsariRockel2024.nelsen7_conditionalCDF` | verified | For every theta,v in [0,1], the actual conditional CDF equals the step with height theta*v+1-theta and, when that height is positive, cutoff (1-theta)*(1-v)/(theta*v+1-theta), almost everywhere in the conditioning coordinate. At zero height the profile is identically zero. |
| Table 6 / Appendix A.5.1: Nelsen 7 derivative correspondence | `Papers.AnsariRockel2024.nelsen7_derivative` | verified | The same step equals the first partial derivative almost everywhere, using the general conditional-CDF bridge; no density hypothesis. |
| Table 6: Nelsen 7 Chatterjee xi | `Papers.AnsariRockel2024.nelsen7_xi` | verified | Xi=1-theta for the entire closed parameter interval, including W at zero and independence at one. |
| Table 3 / Appendix A.1.1: Nelsen 7 exact CI region | `Papers.AnsariRockel2024.nelsen7_ci_iff` | verified | CI iff theta=1. Complements the existing full-interval CD theorem; no interior or positivity restriction. |
| Table 3 / Appendix A.1.2: exact Nelsen 7 Schur order | `Papers.AnsariRockel2024.nelsen7_schur_iff` | verified | Schur comparison in both directions holds iff the parameters are reversely ordered: C_theta precedes C_eta iff eta<=theta, including both endpoints. Uses continuous convex tests of conditional CDFs. |
| Lemmas 2.6(i) and 2.8(i): comparison with monotone copulas | `Papers.AnsariRockel2024.schur_below_cis`; `Papers.AnsariRockel2024.schur_below_cds` | verified | For arbitrary C and CIS D, C<=Schur D implies C<=LO D. For CDS D it implies D<=LO C. No monotonicity or density hypothesis is added for C. Convex hinge tests and an antitone version of the comparator kernel prove the bound. |
| Lemmas 2.6(ii) and 2.8(ii): exact monotone-class order equivalences | `Papers.AnsariRockel2024.cis_schur_iff_orthant`; `Papers.AnsariRockel2024.cds_schur_iff_reverse_orthant` | verified | For any two CIS copulas, Schur order is equivalent to lower orthant order; for two CDS copulas it is equivalent to reversed lower orthant order. A finite convex-majorization theorem and L1 convergence of row averages prove all continuous convex tests. No density or smoothness hypothesis. |
| Proposition 3.2: all three survival invariances | `Papers.AnsariRockel2024.survival_lowerOrthant_iff`; `Papers.AnsariRockel2024.survival_cis_iff`; `Papers.AnsariRockel2024.survival_schur_iff` | verified | Lower orthant order, directional CIS and directional Schur order are preserved and reflected by taking survival copulas. All bivariate copulas, including singular laws. |
| Lemma 2.9: concordance consistency in copula form | `Papers.AnsariRockel2024.concordance_coefficients_mono` | verified | Lower orthant comparison implies both rho and tau comparison, for all bivariate copulas. |
| Lemma 2.10: copula specialization | `Papers.AnsariRockel2024.schur_xi_mono` | verified | Directional conditional-CDF Schur order implies xi comparison. This is the continuous-margin copula specialization; the general arbitrary-margin random-variable statement is not claimed by this row. |
| Lemma 2.12: both tail coefficients | `Papers.AnsariRockel2024.lower_tail_mono`; `Papers.AnsariRockel2024.upper_tail_mono` | verified | Lower orthant comparison implies comparison of both tail limits when the limits exist. No assumption that every copula has such limits. |
| Equation (3): Pickands representation from max-stability | `Papers.AnsariRockel2024.extremeValue_pickands_representation` | verified | An actual max-stable bivariate copula determines its canonical Pickands function by a logarithmic ray; the representation is proved, not assumed. No density or differentiability hypothesis. |
| Theorem 3.4(i)-(ii): Pickands and orthant order | `Papers.AnsariRockel2024.extremeValue_pickands_order` | verified | Lower orthant comparison is equivalent to reverse pointwise comparison of the associated Pickands functions on (0,1). Parts (iii)-(v) for arbitrary extreme-value copulas remain pending. |
| Theorem 3.4(iv)-(v): each directional Schur/Pickands equivalence under CI | `Papers.AnsariRockel2024.extremeValue_schur_first_iff_pickands_of_ci`; `Papers.AnsariRockel2024.extremeValue_schur_second_iff_pickands_of_ci` | verified | Each conditional-CDF Schur direction individually is equivalent to reverse Pickands order for two extreme-value copulas independently known CI. The unconditional five-way equivalence still needs a proof that all bivariate extreme-value copulas are CI. |
| Remark 3.5: ordered rank coefficients | `Papers.AnsariRockel2024.extremeValue_pickands_concordance_mono`; `Papers.AnsariRockel2024.extremeValue_pickands_xi_mono_of_ci` | verified | Reverse Pickands order raises rho and tau unconditionally; it raises xi in both conditioning directions when both copulas are CI. The lower-tail limit is the power-diagonal endpoint indicator; upper-tail limit is 2 minus the extremal coefficient. This does not claim unconditional xi ordering. |
| Remark 3.5: ordered tail coefficients | `Papers.AnsariRockel2024.extremeValue_pickands_tail_mono` | verified | Reverse Pickands order raises both extreme-value tail coefficients, including the comonotonic endpoint. Every bivariate extreme-value copula has both limits by the proved power-diagonal theorem. |
| Theorem 3.4(iii): Schur/Pickands bridge under CI | `Papers.AnsariRockel2024.extremeValue_schur_iff_pickands_of_ci` | verified | For two extreme-value copulas that are independently known CI, reverse Pickands order is equivalent to both directional copula Schur comparisons. The general theorem still requires a proof that every bivariate extreme-value copula is CI. |
| Table 1: Marshall-Olkin CDF | `Papers.AnsariRockel2024.marshallOlkin_cdf` | verified | The minimum of the two power products on the entire closed square, including zero coordinates and parameter endpoints. |
| Table 5 / Appendix A.2: Marshall-Olkin CI and orders | `Papers.AnsariRockel2024.marshallOlkin_ci`; `Papers.AnsariRockel2024.marshallOlkin_orthant_mono`; `Papers.AnsariRockel2024.marshallOlkin_schur_mono` | verified | Both conditional directions are increasing, and coordinatewise parameter increase raises lower orthant order and both Schur orders. Singular laws and all weights in [0,1] included. |
| Table 5 / Appendix A.2: Cuadras-Auge CI and orders | `Papers.AnsariRockel2024.cuadrasAuge_ci`; `Papers.AnsariRockel2024.cuadrasAuge_orthant_mono`; `Papers.AnsariRockel2024.cuadrasAuge_schur_mono` | verified | The entire parameter interval [0,1] is CI and increasing in lower orthant and both-direction Schur order. |
| Appendix A.5: Cuadras-Auge conditional CDF | `Papers.AnsariRockel2024.cuadrasAuge_conditionalCDF` | verified | The explicit piecewise version is identified with the actual copula's conditional law almost everywhere, using CDF derivatives away from the diagonal. All delta in [0,1]. |
| Table 6 / Appendix A.5: Cuadras-Auge rho and xi | `Papers.AnsariRockel2024.cuadrasAuge_rho`; `Papers.AnsariRockel2024.cuadrasAuge_xi` | verified | Exact rho=3*delta/(4-delta) and xi=delta^2/(2-delta), with independent integration of the CDF and squared conditional CDF. Both endpoints included. |
| Table 6: Cuadras-Auge Kendall tau | `Papers.AnsariRockel2024.cuadrasAuge_tau` | verified | Exact tau=delta/(2-delta) for every delta in [0,1]. The proof derives the conditional-CDF product identity by disintegration and Fubini for arbitrary copulas, then evaluates the symmetric triangle integral; it does not assume a density. Together with the preceding row, all three Table 6 coefficients for this family are checked. |
| Table 5: Marshall-Olkin density TP2 and absolute continuity | `Papers.AnsariRockel2024.marshallOlkin_density_tp2`; `Papers.AnsariRockel2024.marshallOlkin_absolutelyContinuous` | verified | Both properties hold exactly when alpha=0 or beta=0. When both weights are positive, the common-shock construction charges a Lebesgue-null power curve. This proves the analytic min(alpha,beta)>0 non-TP2 entry, not the incompatible numerical-only max(alpha,beta)>0 claim. |
| Table 6: Marshall-Olkin Spearman rho | `Papers.AnsariRockel2024.marshallOlkin_rho` | verified | Exact rho=3 alpha beta/(2 alpha+2 beta-alpha beta) for every alpha,beta in [0,1], including both independence axes and singular positive-weight laws. Derived by splitting the CDF integral at its parameter-dependent power curve. |
| Appendix A.5.2: Marshall-Olkin conditional CDF | `Papers.AnsariRockel2024.marshallOlkin_conditionalCDF` | verified | For alpha>0, the explicit piecewise version agrees almost everywhere with the actual conditional law; the moving power-curve value is irrelevant. |
| Table 6 / Appendix A.5.2: Marshall-Olkin Chatterjee xi | `Papers.AnsariRockel2024.marshallOlkin_xi` | verified | Exact xi=2 alpha^2 beta/(3 alpha+beta-2 alpha beta) for all alpha,beta in [0,1], including both independence axes, the alpha=1/2 case, and singular positive-weight laws. Derived by integrating the squared actual conditional CDF. |
| Table 6: Marshall-Olkin Kendall tau | `Papers.AnsariRockel2024.marshallOlkin_tau` | verified | Exact tau=alpha beta/(alpha+beta-alpha beta) for all alpha,beta in [0,1], including both independence axes, beta=1, and singular positive-weight laws. Derived from the conditional-CDF product identity and a power-curve split; no density assumption. All three Table 6 coefficients for this family are now checked. |
| Table 4: Marshall-Olkin independence axes | `Papers.AnsariRockel2024.marshallOlkin_independence_axes` | verified | Either zero weight gives the independence copula, even if the other weight is positive. |
| Table 5: Cuadras-Auge density TP2 and absolute continuity | `Papers.AnsariRockel2024.cuadrasAuge_density_tp2`; `Papers.AnsariRockel2024.cuadrasAuge_absolutelyContinuous` | verified | Both hold exactly at delta=0. Every positive parameter charges the diagonal, including the delta=1 endpoint. |
| Remaining family constructors and table entries | — | pending | Unlisted cells are not covered by the results above. |
| General dependence/order equivalences and their applications | — | pending | Unlisted density properties and rearrangement-based Schur order need separate correspondence checks. |
| Journal/preprint correspondence | — | pending | Selected named results and four printed discrepancies are compared with the open-access published PDF in SOURCE_COMPARISON.md. The remaining family cells and full version correspondence are not yet checked. |

Proof sources: [ClaytonDensityDerivative.lean](ClaytonDensityDerivative.lean), [Definitions.lean](Definitions.lean),
[Association.lean](Association.lean), and [Dependence.lean](Dependence.lean).

## Source discrepancies and exclusions

The Fréchet simplex and Mardia W-weight above follow the valid copula
mixtures. The reversed simplex inequality and negative W-weight printed in
Appendix A.4.1 / equation (23) are not asserted as theorems. Table 6's
coefficient formulas are checked with the valid family definitions. The corrected
Frechet lower orthant order and an explicit counterexample to the printed
increasing-in-W-weight direction are also mapped above.

The Mardia CI/CD classifications include independence at theta=0, which is
omitted in the printed endpoint classifications. Density TP2 here means
existence of a TP2 density with respect to square Lebesgue measure, as in
the source's density definition. Both families have such a density exactly
at independence: every nonzero M or W weight puts positive mass on a
Lebesgue-null diagonal. Thus the printed TP2 claims at singular endpoints
are corrected, not asserted. This does not classify alternative notions of
total positivity for singular measures or for the CDF.

Other discrepancies documented in the pinned library's
[coverage audit](https://github.com/Corrram/copula/blob/765dfec9bdd19c41414738718e818f25e2fe825f/docs/ansari-rockel.md)
remain outside this verified subset. Numerical plots, grid searches, and
numerical-only table observations are excluded from the formal claims.

Additional proof modules: [FamilyExtensions.lean](FamilyExtensions.lean), [TailsAndOrders.lean](TailsAndOrders.lean), and [FrechetMardiaDependence.lean](FrechetMardiaDependence.lean). Shared measure and dependence proofs are in [Verification/FrechetDependence.lean](../../Verification/FrechetDependence.lean).

[Nelsen7Results.lean](Nelsen7Results.lean) maps the new pinned-library results. The Frechet/Mardia proof modules now delegate to the upstream package; their existing public declarations and audits are preserved.
