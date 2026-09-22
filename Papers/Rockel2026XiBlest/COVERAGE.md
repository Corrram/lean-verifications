# Coverage

**Status: in progress.** Blest normalization, range, mixtures, reflection symmetry, the xi=0 endpoint, entire xi=1 boundary, convexity of the full region, and attainment from any existing point up to xi=1 at fixed Blest value are checked. Closedness, compactness, and attainment of both Blest extrema at each xi and the least xi at each Blest value are now checked. The clamped extremal family, its unique normalization, and unique Blest maximality at each constructed positive-slope point are checked. Every intermediate xi value is reached, and the full region is characterized by the constructed family with unique upper boundary copulas. Explicit coefficient formulas, strict parameter monotonicity, the numerical maximal gap, and journal comparison remain pending.

## Source and conventions

Source: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
Journal reference: [DOI 10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744); version comparison pending.

Blest weights the first coordinate by 1-u, exactly as in equation (3). The product uniform measure is proved to give the displayed iterated integral. All integrals exist for arbitrary copulas, including singular ones. Xi conditions coordinate 1 on coordinate 0, with the derivative bridge checked in equation (2). Pi/M/W benchmarks and the full range [-1,1] are checked. Reflection of the second coordinate preserves xi and negates nu. The extremal construction and optimization results are mapped separately below. No sign-reversal claim is made for reflection of the first coordinate.

The vertical boundary is obtained using the proved identity nu=rho for radially symmetric copulas and centered deterministic witnesses with rho=1-2 alpha^3. The clamped family and its sharp optimization certificate are now proved; its coefficient formulas remain a separate obligation.

Convexity is proved independently of the curved boundary formulas. A first copula mixture preserves the desired affine coefficient and gives xi no larger than the target convex combination. A second mixture with a proved xi=1 witness at the same coefficient reaches the target xi by continuity. Both steps construct actual copulas, including singular laws and endpoint weights. This also proves attainment of every xi between an existing point and 1 at fixed coefficient; closedness and attainment of slice extrema are proved separately below.

## Result map

Proofs are in [Blest.lean](Blest.lean), [Normalization.lean](Normalization.lean), [RightBoundary.lean](RightBoundary.lean), [RegionGeometry.lean](RegionGeometry.lean),, [ClosedRegion.lean](ClosedRegion.lean), [ConditionalFormula.lean](ConditionalFormula.lean), [Optimization.lean](Optimization.lean),, [ExtremalFamily.lean](ExtremalFamily.lean), [ParameterCoverage.lean](ParameterCoverage.lean), and [ParametricRegion.lean](ParametricRegion.lean), imported by
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
| Theorem 1.1: attainment up to xi=1 at fixed Blest nu | `Papers.Rockel2026XiBlest.fixed_coefficient_upward` | verified | Every attained (x,y) extends to all (z,y) with x<=z<=1. Uses an actual xi=1 witness at the same coefficient and a continuous copula-mixture path. |
| Theorem 1.1: convexity of the entire attainable region | `Papers.Rockel2026XiBlest.attainable_region_convex` | verified | Every convex combination of attainable pairs is attained. Independent two-mixture proof; no assumed curved-boundary formula or full-region characterization. |
| Theorem 2.3 and Section 4 coefficient formulas | — | pending | Derive the piecewise xi/Blest expressions and endpoint limits. |
| Theorem 1.1: remaining boundary and full region | — | pending | Derive the explicit coefficient formulas, strict parameter monotonicity, and numerical maximal gap. Parameter exhaustion and the exact region in terms of constructed copulas are checked below. Closedness and abstract attainment of all slice extrema are separately verified below. |
| Equation (3): reversed integration order | `Papers.Rockel2026XiBlest.blest_integral_formula_swapped` | verified | Fubini and integrability for the weighted CDF of every copula. |
| After equation (3): M/W normalization and range | `Papers.Rockel2026XiBlest.blest_comonotonic`; `Papers.Rockel2026XiBlest.blest_countermonotonic`; `Papers.Rockel2026XiBlest.blest_mem_Icc` | verified | Nu(M)=1, nu(W)=-1, and -1<=nu(C)<=1 for every copula. |
| Equation (13) and the following xi calculation | `Papers.Rockel2026XiBlest.blest_reflect_second`; `Papers.Rockel2026XiBlest.xi_blest_reflection` | verified | Reflecting coordinate 1 preserves xi and negates Blest's nu, including singular copulas. |
| Theorem 1.1: continuity of Blest under CDF convergence | `Papers.Rockel2026XiBlest.blest_tendsto_of_cdf` | verified | Pointwise CDF convergence of arbitrary copulas implies convergence of the exact weighted functional. |
| Theorem 1.1: closedness and compactness | `Papers.Rockel2026XiBlest.attainable_region_closed`; `Papers.Rockel2026XiBlest.attainable_region_compact` | verified | Entire attained region. Independent proof using weak compactness, lower semicontinuity of xi, and fixed-Blest upward interpolation. |
| Theorem 1.1: attained slice extrema | `Papers.Rockel2026XiBlest.blest_extrema_attained`; `Papers.Rockel2026XiBlest.minimal_xi_attained` | verified | Both Blest extrema exist for each xi in [0,1]; the least xi exists for every Blest value in [-1,1]. Does not yet identify the extremal family, prove its formulas, or assert uniqueness. |
| Journal/preprint correspondence | — | pending | Only arXiv v1 is mapped. |

| Equation (16): conditional integral identity | `Papers.Rockel2026XiBlest.blest_conditional_formula` | verified | Every copula, including singular laws; the squared first-coordinate weight is proved by Fubini. |
| Lemma 2.1: unique normalization | `Papers.Rockel2026XiBlest.extremal_normalization` | verified | Every b>0 and v in [0,1]; unique q in [-1/b,1]. |
| Lemma 2.1: ordered, measurable conditional sections | `Papers.Rockel2026XiBlest.extremalQ_antitone`; `Papers.Rockel2026XiBlest.extremal_kernel_measurable` | verified | Antitone q and joint measurability of the actual normalized kernel. |
| Lemma 2.2: constructed copula and derivative bridge | `Papers.Rockel2026XiBlest.extremal_cdf`; `Papers.Rockel2026XiBlest.extremal_conditionalCDF`; `Papers.Rockel2026XiBlest.extremal_isSI` | verified | The clamped kernel constructs an actual copula; CDF formula, almost-everywhere conditional identity, and stochastic monotonicity. |
| Theorem 1.1: sharp quantitative optimization certificate | `Papers.Rockel2026XiBlest.clamped_blest_distance_bound`; `Papers.Rockel2026XiBlest.extremal_support`; `Papers.Rockel2026XiBlest.extremal_support_eq_iff` | verified | All competing copulas. The support deficit bounds squared conditional-CDF distance and equality forces the constructed copula. |
| Theorem 1.1: unique maximum at every constructed positive-slope point | `Papers.Rockel2026XiBlest.extremal_maximal_blest`; `Papers.Rockel2026XiBlest.extremal_maximal_blest_eq_iff` | verified | Blest maximality for xi no greater than the constructed point; equality characterization at the same xi. Exhaustion of all intermediate xi values is proved below. |
| Theorem 1.1: independence endpoint of the constructed family | `Papers.Rockel2026XiBlest.extremal_zero` | verified | The b=0 extension is exactly the independence copula. |

| Theorem 1.1: monotonicity of the extremal coefficients | `Papers.Rockel2026XiBlest.extremal_coefficients_monotone` | verified | Both xi and Blest are nondecreasing in the nonnegative slope; strict parameter monotonicity remains separate. |
| Theorem 1.1: continuous xi parameter | `Papers.Rockel2026XiBlest.extremal_xi_continuous` | verified | The entire nonnegative parameter interval, including zero; proved with the quantitative bound |xi(b)-xi(d)|<=24|b-d|. |
| Theorem 1.1: comonotonic endpoint | `Papers.Rockel2026XiBlest.extremalSequence_cdf`; `Papers.Rockel2026XiBlest.extremalSequence_xi`; `Papers.Rockel2026XiBlest.extremalSequence_blest` | verified | The cofinal sequence b=(n+1)^2 converges in CDF, xi, and Blest to the comonotonic endpoint. The uniform CDF error is at most 1/(n+1). |
| Theorem 1.1: all intermediate xi parameters are attained | `Papers.Rockel2026XiBlest.extremal_parameter_exists` | verified | Every x in (0,1) is the xi of an actual positive-slope member; proved by continuity and the checked endpoint limit. |
| Theorem 1.1: exact attainable slices | `Papers.Rockel2026XiBlest.extremal_slice_iff`; `Papers.Rockel2026XiBlest.intermediate_slice_characterization` | verified | For every intermediate xi, the full Blest slice is exactly the interval between the reflected constructed boundaries. Actual copula witnesses fill the interval; the upper boundary copula is unique. Explicit coefficient formulas remain pending. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
