# Coverage

**Status: in progress.** The exact xi-Blest region, both explicit coefficient branches, endpoint limits, unique curved-boundary copulas and parameters, convexity, compactness, and the sharp gap 44/105 are checked. The relaxed measurable-kernel optimization problem, normalization-map continuity, and derivative identity including b=1 are also checked. All main and auxiliary results specific to arXiv v1 are checked, including Lemmas 4.1-4.2. A displayed intermediate polynomial is formally refuted and corrected; the final coefficient formulas are verified independently. Comparison with the journal version remains pending.

## Source and conventions

Source: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
Journal reference: [DOI 10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744); version comparison pending.

Blest weights the first coordinate by 1-u, exactly as in equation (3). The product uniform measure is proved to give the displayed iterated integral. All integrals exist for arbitrary copulas, including singular ones. Xi conditions coordinate 1 on coordinate 0, with the derivative bridge checked in equation (2). Pi/M/W benchmarks and the full range [-1,1] are checked. Reflection of the second coordinate preserves xi and negates nu. The extremal construction and optimization results are mapped separately below. No sign-reversal claim is made for reflection of the first coordinate.

The vertical boundary is obtained using the proved identity nu=rho for radially symmetric copulas and centered deterministic witnesses with rho=1-2 alpha^3. The clamped family and its sharp optimization certificate are now proved; both coefficient branches are now derived from exact integrals of the constructed family.

Convexity is proved independently of the curved boundary formulas. A first copula mixture preserves the desired affine coefficient and gives xi no larger than the target convex combination. A second mixture with a proved xi=1 witness at the same coefficient reaches the target xi by continuity. Both steps construct actual copulas, including singular laws and endpoint weights. This also proves attainment of every xi between an existing point and 1 at fixed coefficient; closedness and attainment of slice extrema are proved separately below.

## Result map

[Main.lean](Main.lean) imports the result modules. [Axioms.lean](Axioms.lean)
prints and enforces the standard transitive axiom allowlist for every declaration below.

The coefficient computation uses a uniform sampling representation, exact clamp-noise
moments, and radical integrals. This is an independent derivation of Theorem 2.3;
the separate section and substitution formulas are also verified below.
The relaxed optimization theorem covers all measurable representatives satisfying
the box and marginal constraints almost everywhere, without a monotonicity assumption.
Uniqueness is equality almost everywhere, as appropriate for L2.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (3): existence of the weighted integral | `Papers.Rockel2026XiBlest.blest_integrable` | verified | All bivariate copulas; no density hypothesis. |
| Equation (3): iterated-integral correspondence | `Papers.Rockel2026XiBlest.blest_integral_formula` | verified | First-coordinate weight 1-u and source integration order. |
| Equation (2): xi derivative convention | `Papers.Rockel2026XiBlest.xi_derivative_formula` | verified | All bivariate copulas; almost-everywhere derivative correspondence. |
| After equation (3): concordance monotonicity | `Papers.Rockel2026XiBlest.blest_mono` | verified | Pointwise CDF ordering implies ordering of Blest coefficients. |
| Equation (3): affine-mixture identity used in the region argument | `Papers.Rockel2026XiBlest.blest_mix` | verified | Any two copulas and every closed-interval mixture weight. |
| After equation (3): independence normalization | `Papers.Rockel2026XiBlest.blest_independence` | verified | Nu(Pi)=0 with the source normalization. |
| Theorem 1.1: xi=0 endpoint | `Papers.Rockel2026XiBlest.xi_zero_slice` | verified | Xi=0 forces the unique copula Pi and nu=0; both curved boundaries and the xi=1 boundary are checked below. |
| Supporting identity for Theorem 1.1 vertical boundary | `Papers.Rockel2026XiBlest.blest_eq_rho_of_radiallySymmetric` | verified | Blest nu equals Spearman rho for every radially symmetric copula. Both uniform-coordinate reflection and weighted-integral identities are proved. |
| Theorem 1.1: entire vertical boundary | `Papers.Rockel2026XiBlest.xi_one_slice` | verified | Exactly nu in [-1,1] is attainable at xi=1. Centered deterministic radially symmetric copulas supply the witnesses; no unproved curved-boundary formula is used. |
| Theorem 1.1: attainment up to xi=1 at fixed Blest nu | `Papers.Rockel2026XiBlest.fixed_coefficient_upward` | verified | Every attained (x,y) extends to all (z,y) with x<=z<=1. Uses an actual xi=1 witness at the same coefficient and a continuous copula-mixture path. |
| Theorem 1.1: convexity of the entire attainable region | `Papers.Rockel2026XiBlest.attainable_region_convex` | verified | Every convex combination of attainable pairs is attained. Independent two-mixture proof; no assumed curved-boundary formula or full-region characterization. |
| Equation (3): reversed integration order | `Papers.Rockel2026XiBlest.blest_integral_formula_swapped` | verified | Fubini and integrability for the weighted CDF of every copula. |
| After equation (3): M/W normalization and range | `Papers.Rockel2026XiBlest.blest_comonotonic`; `Papers.Rockel2026XiBlest.blest_countermonotonic`; `Papers.Rockel2026XiBlest.blest_mem_Icc` | verified | Nu(M)=1, nu(W)=-1, and -1<=nu(C)<=1 for every copula. |
| Equation (13) and the following xi calculation | `Papers.Rockel2026XiBlest.blest_reflect_second`; `Papers.Rockel2026XiBlest.xi_blest_reflection` | verified | Reflecting coordinate 1 preserves xi and negates Blest's nu, including singular copulas. |
| Theorem 1.1: continuity of Blest under CDF convergence | `Papers.Rockel2026XiBlest.blest_tendsto_of_cdf` | verified | Pointwise CDF convergence of arbitrary copulas implies convergence of the exact weighted functional. |
| Theorem 1.1: closedness and compactness | `Papers.Rockel2026XiBlest.attainable_region_closed`; `Papers.Rockel2026XiBlest.attainable_region_compact` | verified | Entire attained region. Independent proof using weak compactness, lower semicontinuity of xi, and fixed-Blest upward interpolation. |
| Theorem 1.1: attained slice extrema | `Papers.Rockel2026XiBlest.blest_extrema_attained`; `Papers.Rockel2026XiBlest.minimal_xi_attained` | verified | Both Blest extrema exist for each xi in [0,1]; the least xi exists for every Blest value in [-1,1]. The extremal family, formulas, and uniqueness are identified by the separate results below. |
| Journal/preprint correspondence | — | pending | Only arXiv v1 is mapped. |
| Equation (16): conditional integral identity | `Papers.Rockel2026XiBlest.blest_conditional_formula` | verified | Every copula, including singular laws; the squared first-coordinate weight is proved by Fubini. |
| Lemma 2.1: unique normalization | `Papers.Rockel2026XiBlest.extremal_normalization` | verified | Every b>0 and v in [0,1]; unique q in [-1/b,1]. |
| Lemma 2.1: ordered, measurable conditional sections | `Papers.Rockel2026XiBlest.extremalQ_antitone`; `Papers.Rockel2026XiBlest.extremal_kernel_measurable` | verified | Antitone q and joint measurability of the actual normalized kernel. |
| Lemma 2.2: constructed copula and derivative bridge | `Papers.Rockel2026XiBlest.extremal_cdf`; `Papers.Rockel2026XiBlest.extremal_conditionalCDF`; `Papers.Rockel2026XiBlest.extremal_isSI` | verified | The clamped kernel constructs an actual copula; CDF formula, almost-everywhere conditional identity, and stochastic monotonicity. |
| Theorem 1.1: sharp quantitative optimization certificate | `Papers.Rockel2026XiBlest.clamped_blest_distance_bound`; `Papers.Rockel2026XiBlest.extremal_support`; `Papers.Rockel2026XiBlest.extremal_support_eq_iff` | verified | All competing copulas. The support deficit bounds squared conditional-CDF distance and equality forces the constructed copula. |
| Theorem 1.1: unique maximum at every constructed positive-slope point | `Papers.Rockel2026XiBlest.extremal_maximal_blest`; `Papers.Rockel2026XiBlest.extremal_maximal_blest_eq_iff` | verified | Blest maximality for xi no greater than the constructed point; equality characterization at the same xi. Exhaustion of all intermediate xi values is proved below. |
| Theorem 1.1: independence endpoint of the constructed family | `Papers.Rockel2026XiBlest.extremal_zero` | verified | The b=0 extension is exactly the independence copula. |
| Theorem 1.1: monotonicity of the extremal coefficients | `Papers.Rockel2026XiBlest.extremal_coefficients_monotone` | verified | Both xi and Blest are nondecreasing in the nonnegative slope; strict parameter monotonicity is verified below. |
| Theorem 1.1: continuous xi parameter | `Papers.Rockel2026XiBlest.extremal_xi_continuous` | verified | The entire nonnegative parameter interval, including zero; proved with the quantitative bound abs(xi(b)-xi(d))<=24 abs(b-d). |
| Theorem 1.1: comonotonic endpoint | `Papers.Rockel2026XiBlest.extremalSequence_cdf`; `Papers.Rockel2026XiBlest.extremalSequence_xi`; `Papers.Rockel2026XiBlest.extremalSequence_blest` | verified | The cofinal sequence b=(n+1)^2 converges in CDF, xi, and Blest to the comonotonic endpoint. The uniform CDF error is at most 1/(n+1). |
| Theorem 1.1: all intermediate xi parameters are attained | `Papers.Rockel2026XiBlest.extremal_parameter_exists` | verified | Every x in (0,1) is the xi of an actual positive-slope member; proved by continuity and the checked endpoint limit. |
| Theorem 1.1: exact attainable slices | `Papers.Rockel2026XiBlest.extremal_slice_iff`; `Papers.Rockel2026XiBlest.intermediate_slice_characterization` | verified | For every intermediate xi, the full Blest slice is exactly the interval between the reflected constructed boundaries. Actual copula witnesses fill the interval; the upper boundary copula is unique. Both explicit coefficient branches are verified below. |
| Theorem 2.3: polynomial coefficient branch | `Papers.Rockel2026XiBlest.extremal_coefficients_polynomial` | verified | Actual extremal copulas for every 0<=b<=1: xi=8b^2(7-3b)/105 and nu=4b(28-9b)/105, including b=0 and b=1. Derived through the proved uniform sampling law and exact integrals. |
| Theorem 2.3: joining point of the two branches | `Papers.Rockel2026XiBlest.extremal_one_coefficients` | verified | At b=1, xi=32/105 and nu=76/105. |
| Theorem 1.1: maximal signed gap and uniqueness | `Papers.Rockel2026XiBlest.maximal_signed_gap`; `Papers.Rockel2026XiBlest.maximal_signed_gap_eq_iff` | verified | For every copula, nu-xi<=44/105; equality holds exactly at the constructed b=1 copula. |
| Theorem 1.1: maximal absolute gap and all equality cases | `Papers.Rockel2026XiBlest.maximal_absolute_gap`; `Papers.Rockel2026XiBlest.maximal_absolute_gap_eq_iff` | verified | For every copula, abs(nu)-xi<=44/105; equality holds exactly at the b=1 copula or its response reflection. |
| Lemma 4.5 and Theorem 1.1: strict coefficient monotonicity | `Papers.Rockel2026XiBlest.extremal_coefficients_strictMono` | verified | Both xi and Blest strictly increase with the nonnegative slope. Proved from slope identifiability and the sharp optimization certificate, independently of the b>1 formulas. |
| Theorem 1.1: finite parameters and unique xi parameter | `Papers.Rockel2026XiBlest.extremal_finite_xi`; `Papers.Rockel2026XiBlest.extremal_positive_xi`; `Papers.Rockel2026XiBlest.extremal_parameter_unique` | verified | Every positive finite slope has xi strictly between 0 and 1; every such xi has exactly one positive parameter. |
| Theorem 2.3: hyperbolic coefficient branch | `Papers.Rockel2026XiBlest.extremal_coefficients_hyperbolic` | verified | For every b>1, both displayed arcosh formulas equal the coefficients of the constructed copula. Exact radical integrals; no assumed coefficient formula. |
| Theorem 2.3 and equations (4)-(5): complete formulas | `Papers.Rockel2026XiBlest.extremal_coefficients` | verified | All b>=0, including the joining point and independence endpoint. |
| Theorem 1.1 and equation (6): explicit exact region | `Papers.Rockel2026XiBlest.exact_region` | verified | Necessary and sufficient conditions, with actual copula witnesses for every point and the full xi=1 vertical segment. |
| Theorem 1.1: unique upper and lower curved boundaries | `Papers.Rockel2026XiBlest.upper_boundary_unique`; `Papers.Rockel2026XiBlest.lower_boundary_unique` | verified | Every finite positive slope; the lower optimizer is precisely the response reflection. |
| Theorem 1.1: endpoint conventions and limits | `Papers.Rockel2026XiBlest.formula_zero`; `Papers.Rockel2026XiBlest.formula_zero_limits`; `Papers.Rockel2026XiBlest.formula_infinity_limits` | verified | Both coefficients equal and tend to zero at b=0, and tend to one as the real parameter tends to infinity. |
| Lemma 4.5 and equation (7): derivative identity | `Papers.Rockel2026XiBlest.formula_hasDerivAt`; `Papers.Rockel2026XiBlest.formula_derivative_identity` | verified | Both functions are differentiable for every b>0, including b=1, and N′(b)=Xi′(b)/b. Differentiation under the exact tail integrals is justified. |
| Lemma 2.1: normalization-map properties | `Papers.Rockel2026XiBlest.normalizationMean_properties`; `Papers.Rockel2026XiBlest.extremalQ_continuous`; `Papers.Rockel2026XiBlest.extremal_kernel_continuous` | verified | Continuous, strictly decreasing normalization map on [-1/b,1], correct endpoints and range, continuous inverse parameter, and jointly continuous kernel. |
| Lemma 4.4: mixture-path continuity | `Papers.Rockel2026XiBlest.xi_mixture_continuous` | verified | All copulas, including singular laws and endpoint mixture weights. |
| Theorem 3.4: relaxed optimization and uniqueness | `Papers.Rockel2026XiBlest.relaxed_distance_bound`; `Papers.Rockel2026XiBlest.relaxed_solution` | verified | All admissible measurable kernels, including those not defining copulas. Every c in (0,1) has a unique positive parameter and a unique optimizer modulo almost-everywhere equality. |
| Lemma 4.1: equations (20)-(22) | `Papers.Rockel2026XiBlest.section_formulas` | verified | All admissible section parameters, including clamp-switching endpoints; exact ordinary, squared, and weighted moments. |
| Lemma 4.1: differentiability and change of variables | `Papers.Rockel2026XiBlest.normalizationMean_hasDerivAt`; `Papers.Rockel2026XiBlest.normalization_substitution` | verified | Differentiation under the integral is justified by a uniform Lipschitz bound and null switching sets. The substitution holds for every continuous section functional. |
| Lemma 4.1: equations (23)-(24) | `Papers.Rockel2026XiBlest.one_dimensional_coefficients` | verified | The one-dimensional integrals equal the actual copula coefficients, using the derivative of the actual normalization map. |
| Lemma 4.2: all four regimes | `Papers.Rockel2026XiBlest.substitution_upper`; `Papers.Rockel2026XiBlest.substitution_unclamped`; `Papers.Rockel2026XiBlest.substitution_double`; `Papers.Rockel2026XiBlest.substitution_lower` | verified | Upper-clamped, unclamped, double-clamped, and lower-clamped substitutions, including shared boundary cases. |
| Proof of Theorem 2.3: corrected lower-clamped square polynomial | `Papers.Rockel2026XiBlest.lower_square_polynomial`; `Papers.Rockel2026XiBlest.printed_lower_square_polynomial_false` | verified | The correct coefficient of r^5 is -8/15. The printed -1/5 is disproved at r=1/2. The final theorem formulas are unaffected and separately verified. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.

Lemma 3.1 is quoted external KKT theory; Lemmas 3.2 and 4.3 are quoted from the xi-rho paper. The independent proofs here do not rely on the KKT or shuffling lemmas. Numerical Table 1 and plots are excluded from the formal theorem scope.

## Corrected intermediate calculation

In the proof of Theorem 2.3, the displayed lower-clamped expression G_iv
subtracts r^5/5. Expanding the preceding definition F(r;r^2) instead gives
8r^5/15. At b=1 and r=1/2, the correct squared section integral is 19/240,
whereas the printed expression gives 43/480. The two Lean declarations above
prove the corrected identity and disprove the printed polynomial. The final
Xi and N formulas and all region statements are proved from the actual copulas.
The literal erroneous intermediate line is not claimed verified.
