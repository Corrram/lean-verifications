# Coverage

**Status: in progress.** Theorems 2.1, 2.4, 3.2, and 3.4, Propositions 2.2, 3.1, and 3.5, and Corollary 2.5 are checked. Theorem 3.3's convexity, entire xi=1 boundary, fixed-footrule interpolation, and exact nonnegative-footrule region are verified. Its inverse lower estimate is checked for footrule in [-1/2,0], with parameter uniqueness on [0,2]. Remark 2.3's asymmetric SI equality example is constructed and checked, including its derivative, xi=footrule=1/2, and asymmetry. The two-parameter density construction is checked on the full closed parameter square, including its independence and checkerboard endpoints. The full region is now proved closed and compact, and every boundary slice attains its extremum. The printed LTD example is proved not LTD; a corrected LTD example with exact ranks is supplied. The exact lower-semilinear region is proved independently of stochastic increase. Finite nested ordinal sums of independence and comonotonic blocks are now proved SI and symmetric with xi=footrule; SI is also preserved by binary ordinal sums, and the interior equality converse is checked for SI components. The full countable ordinal-sum classification and journal-version comparison remain pending.

## Source and proof scope

Source: [arXiv:2509.07232v1](https://arxiv.org/html/2509.07232v1).
Comparison with the [journal version](https://doi.org/10.1016/j.cam.2026.117466)
remains pending.

The proof uses an exact squared-distance identity for conditional CDFs:
for the Fréchet mixture $D_a=(1-a)\Pi+aM$,

$$
6\int_0^1\int_0^1(K_C(u,v)-K_{D_a}(u,v))^2\,du\,dv
=\xi(C)+a^2-2a\psi(C).
$$

Nonnegativity gives the bound. Vanishing distance identifies the copula,
which proves uniqueness, including the endpoints. This is an alternative
proof of the result: it does not claim to formalize the paper's KKT argument
or its general optimization lemmas.

## Source correspondence

The copula is represented as a probability measure with uniform marginals.
The explicit CDF of the extremizing family is proved below. Footrule is
$6\int_0^1 C(t,t)\,dt-2$, with range $[-1/2,1]$.
Xi conditions coordinate 1 on coordinate 0. The derivative formula from
equation (1) is checked via the almost-everywhere fundamental theorem of
calculus; no density assumption is added. The auxiliary constant extension
of a CDF section outside $[0,1]$ has the same derivative in the interior;
the two endpoints have zero measure.

The lower endpoint has an independent proof through the sharp xi-beta theorem in the companion supplement; the source checkerboard is identified by its explicit CDF. This avoids assuming a general checkerboard approximation inequality.

For Proposition 2.2, the equality case of the scalar diagonal moment bound is proved by a nonnegative algebraic defect. At almost every response threshold, it forces the antitone conditional-CDF section to take only the values 1, one intermediate level, and 0 almost everywhere. The canonical cut functions are the lengths of its one and positive level sets. Monotonicity in the response threshold proves that both cuts are nondecreasing and hence measurable. The uniform marginal determines the measurable middle level, with coincident cuts handled separately. The representation uses precisely the source's open intervals and nested almost-everywhere quantifiers. Both necessity and sufficiency are proved, including the first-partial-derivative formulation. No density assumption is imposed. The source's Lebesgue-Stieltjes integration-by-parts argument is not separately claimed verified.

For Theorem 3.2, a two-bin squared-distance identity proves the Jensen bound and its almost-everywhere equality criterion. An exact quadratic remainder proves that the source's piecewise pair is the global minimizer of the relaxed scalar problem, uniquely at every interior response threshold. The profile is measurable and feasible for all mu in [0,2], including the cutoff and parameter endpoints. Integrating the estimate proves the universal weighted bound for arbitrary copulas. The relaxed coefficients are defined by the exact kernel/CDF integrals with the source's normalization; Proposition 3.1's logarithmic closed forms, strict monotonicity, continuity, and endpoint values are now evaluated from those same integrals. This independent proof does not assert the source KKT argument separately.

The relaxed primitive is deliberately a real-valued function rather than a copula. A formal counterexample at mu=2 proves that it decreases in the second coordinate: its values at (3/10,1/5) and (3/10,3/10) are respectively 1/40 and 0. Thus the proved relaxed lower bound does not claim copula attainment.

The parameter inversion in Theorem 3.3 is proved for footrule y in [-1/2,0], with a unique parameter mu in [0,2]. This restriction matters: at y=-1/2 the cubic factors as (mu-2)^2(mu+1), so its real roots are not globally unique. The formal counterexample below records the correction to the source wording. The inverse estimate does not assert that the relaxed profile attains the copula boundary.

Convexity is proved independently of the curved boundary formulas. A first copula mixture preserves the desired affine coefficient and gives xi no larger than the target convex combination. A second mixture with a proved xi=1 witness at the same coefficient reaches the target xi by continuity. Both steps construct actual copulas, including singular laws and endpoint weights. This also proves attainment of every xi between an existing point and 1 at fixed coefficient; closedness and attainment of slice extrema are proved separately below.

## Result map

Source references use arXiv v1 unless explicitly marked JCAM resubmission; see [SOURCE_COMPARISON.md](SOURCE_COMPARISON.md). Proofs are in
[Definitions.lean](Definitions.lean), [UpperBoundary.lean](UpperBoundary.lean), [LowerEndpoint.lean](LowerEndpoint.lean), [SIRegion.lean](SIRegion.lean), [SIEquality.lean](SIEquality.lean), [AsymmetricEquality.lean](AsymmetricEquality.lean), [LowerBound.lean](LowerBound.lean), [ClosedCoefficients.lean](ClosedCoefficients.lean), [RegionGeometry.lean](RegionGeometry.lean), [TwoParameter.lean](TwoParameter.lean), [ClosedRegion.lean](ClosedRegion.lean), and [LTDExample.lean](LTDExample.lean).
[Axioms.lean](Axioms.lean) prints and enforces the transitive axiom allowlist.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (1): xi in the source derivative convention | `Papers.Rockel2026XiFootrule.xi_derivative_formula` | verified | Every bivariate copula; equality almost everywhere, with constant extension of CDF sections outside the unit interval. |
| Theorem 2.1: the Fréchet extremizer's CDF | `Papers.Rockel2026XiFootrule.cdf_upperBoundary` | verified | Entire closed square and parameter interval. |
| Theorem 2.1: universal bound, attainment, and unique maximizer | `Papers.Rockel2026XiFootrule.maximal_footrule` | verified | Every prescribed xi in [0,1]; all bivariate copulas, including singular copulas and both endpoints. |
| After Theorem 2.1 / Table 1: sharp upper bound on footrule minus xi | `Papers.Rockel2026XiFootrule.footrule_sub_xi_le` | verified | All bivariate copulas; the bound is 1/4. |
| After Theorem 2.1 / Table 1: unique equality case | `Papers.Rockel2026XiFootrule.footrule_sub_xi_eq_iff` | verified | Equality precisely at the half-independence, half-comonotonic mixture. |
| Lemmas A.1–A.2 and the paper's KKT proof strategy | — | excluded | The theorem above has an independent squared-distance proof. |
| Theorem 3.4: checkerboard construction and values | `Papers.Rockel2026XiFootrule.antiCheckerboard_cdf`; `Papers.Rockel2026XiFootrule.antiCheckerboard_xi`; `Papers.Rockel2026XiFootrule.antiCheckerboard_footrule` | verified | CDF on the full square equals the integral of density two on the two off-diagonal median cells; xi=1/2 and footrule=-1/2. |
| Theorem 3.4: sharp minimum and unique minimizer | `Papers.Rockel2026XiFootrule.xi_lower_bound_at_minimal_footrule`; `Papers.Rockel2026XiFootrule.xi_minimum_at_minimal_footrule_iff` | verified | Every copula with footrule=-1/2 has xi>=1/2, with equality exactly at the checkerboard. Alternative proof using the verified xi-beta bound and equality theorem. |
| Section 3.1: complete bottom boundary | `Papers.Rockel2026XiFootrule.exact_bottom_boundary` | verified | A pair (x,-1/2) is attained if and only if x is in [1/2,1]. Attainment uses fixed-footrule mixtures of the checkerboard and W. |
| Theorem 2.4: SI lower bound | `Papers.Rockel2026XiFootrule.si_xi_le_footrule` | verified | Every SI copula, including singular laws. An antitone version of each conditional CDF gives its squared integral below C(v,v); integrating proves xi<=footrule. |
| Theorem 2.4: lower-boundary witnesses | `Papers.Rockel2026XiFootrule.diagonalBoundary_cdf`; `Papers.Rockel2026XiFootrule.diagonalBoundary_isSI`; `Papers.Rockel2026XiFootrule.diagonalBoundary_coefficients` | verified | The ordinal sum of independence below a and M above a is SI and has xi=footrule=1-a^2. The full-square CDF and the closed parameter interval, including a=0 and a=1, are proved. |
| Theorem 2.4: upper witnesses and entire SI region | `Papers.Rockel2026XiFootrule.upperBoundary_isSI`; `Papers.Rockel2026XiFootrule.exact_si_xi_footrule_region` | verified | A pair (x,y) is attained by an SI copula iff x,y are in [0,1] and x<=y<=sqrt(x). Mixtures with equal footrule remain SI and a proved continuous xi path attains every interior point. |
| Corollary 2.5: Kendall bound | `Papers.Rockel2026XiFootrule.si_xi_le_three_quarters_tau` | verified | Every SI copula satisfies xi<=3 tau/4+1/4, combining the new SI lower bound with the verified universal tau-footrule bound. |
| Proposition 2.2, equation (12): equality of section moments | `Papers.Rockel2026XiFootrule.si_equality_iff_diagonal_moments` | verified | For every SI copula, xi=footrule iff the squared conditional-CDF integral equals C(v,v) for almost every threshold v. |
| Proposition 2.2: explicit measurable equality witnesses | `Papers.Rockel2026XiFootrule.si_equality_canonical_parameters` | verified | Canonical nondecreasing, measurable cuts A(v)<=v<=B(v), and measurable middle level in [0,1], give the source's three-level representation almost everywhere. Includes coincident cuts and parameter endpoints. |
| Proposition 2.2: full SI equality classification | `Papers.Rockel2026XiFootrule.si_equality_iff_conditional_threeLevel`; `Papers.Rockel2026XiFootrule.si_equality_iff_derivative_threeLevel` | verified | Necessity and sufficiency of the source's measurable three-level representation, in both conditional-CDF and first-partial-derivative conventions. A and B are nondecreasing; all parameters take values in [0,1]. Every SI copula is covered, including singular laws; no family restriction. |
| Remark 2.3: actual asymmetric equality copula | `Papers.Rockel2026XiFootrule.asymmetricEquality_cdf`; `Papers.Rockel2026XiFootrule.asymmetricEquality_isSI` | verified | Construct a copula from the displayed CDF (1-v) min(u,v/2)+v min(u,(v+1)/2); prove uniform margins, nonnegative rectangle increments, and SI. Entire closed square, including endpoint thresholds. |
| Remark 2.3: conditional-CDF and first-derivative correspondence | `Papers.Rockel2026XiFootrule.asymmetricEquality_conditionalCDF`; `Papers.Rockel2026XiFootrule.asymmetricEquality_derivative` | verified | For every v, the source's open-interval three-level profile holds almost everywhere in u. The closed-cut monotone version differs only on the two null cut sets. No density assumption. |
| Remark 2.3: equality and exact coefficient values | `Papers.Rockel2026XiFootrule.asymmetricEquality_xi_eq_footrule`; `Papers.Rockel2026XiFootrule.asymmetricEquality_coefficients` | verified | The constructed SI copula satisfies xi=footrule, with both coefficients exactly 1/2. |
| Remark 2.3: asymmetry | `Papers.Rockel2026XiFootrule.asymmetricEquality_asymmetry_witness`; `Papers.Rockel2026XiFootrule.asymmetricEquality_not_exchangeable` | verified | C(1/4,1/2)=1/4 whereas C(1/2,1/4)=7/32; hence the copula is not exchangeable. |
| Remark 2.3: finite symmetric ordinal sums | `Papers.Rockel2026XiFootrule.ordinalSum_xi_eq_footrule_of_components`; `Papers.Rockel2026XiFootrule.ordinalSum_xi_eq_footrule_iff`; `Papers.Rockel2026XiFootrule.ordinalSum_isSI`; `Papers.Rockel2026XiFootrule.FinitePiOrdinal.symmetric_rank_equality`; `Papers.Rockel2026XiFootrule.FinitePiOrdinal.isSI`; `Papers.Rockel2026XiFootrule.FinitePiOrdinal.symmetric_si_rank_equality` | verified | Binary ordinal sums preserve xi=footrule; with SI components and an interior split, equality holds iff it holds in both components. Every finite recursively nested ordinal sum of Pi and M blocks is SI, exchangeable and has xi=footrule. Binary ordinal sums preserve SI even for arbitrary SI components. No converse or countable classification is asserted. |
| Remark 2.3: general symmetric refinement | — | pending | The characterization of all symmetric SI equality copulas as arbitrary countable ordinal sums of independence remains unproved. |
| Equations (18) and (23): piecewise relaxed profile and feasibility | `Papers.Rockel2026XiFootrule.jensen_profile_formula`; `Papers.Rockel2026XiFootrule.jensen_profile_feasible` | verified | The source's exact cutoffs and formulas; both levels lie in [0,1] and have weighted mean v. Every mu in [0,2] and v in [0,1], including all junctions and endpoints. |
| Equation (22): scalar minimum and uniqueness | `Papers.Rockel2026XiFootrule.scalar_optimizer_minimum`; `Papers.Rockel2026XiFootrule.scalar_optimizer_unique` | verified | Global minimum over every feasible pair; unique for 0<v<1. An explicit quadratic remainder replaces the KKT proof. No uniqueness is claimed for the zero-weight coordinate at v=0 or v=1. |
| Equation (20): Jensen bound and equality | `Papers.Rockel2026XiFootrule.conditional_jensen_bound`; `Papers.Rockel2026XiFootrule.conditional_jensen_equality` | verified | Every copula and 0<v<1. Equality iff the conditional CDF is almost everywhere equal to its two bin averages. Singular copulas are included. |
| Equations (17)-(18): extended coefficient normalization | `Papers.Rockel2026XiFootrule.relaxed_values_integral_form` | verified | The relaxed primitive and kernel yield exactly the source's footrule and xi integral normalizations. They are real-valued functions; no copula assumption is introduced. |
| Theorem 3.2: universal weighted lower bound | `Papers.Rockel2026XiFootrule.weighted_lower_bound` | verified | Every copula and mu in [0,2]: mu times footrule plus xi is bounded below by the corresponding relaxed-profile value. The relaxed coefficients are specified by exact integrals; the closed-form evaluation is verified below. |
| Theorem 3.3: parameterized fixed-footrule consequence | `Papers.Rockel2026XiFootrule.xi_lower_bound_at_relaxed_footrule` | verified | If a copula's footrule equals the relaxed value at a supplied mu in [0,2], its xi is at least the relaxed xi. Existence and uniqueness of the matching parameter for target footrule in [-1/2,0] are verified below. |
| After equation (18): the relaxed family is not a copula family | `Papers.Rockel2026XiFootrule.relaxed_family_not_copula` | verified | At mu=2 the primitive fails CDF monotonicity in the second coordinate. The relaxation is not advertised as an attaining copula family. |
| Proposition 3.1: exact closed coefficient formulas | `Papers.Rockel2026XiFootrule.relaxed_coefficients_closed` | verified | Evaluate the existing relaxed integrals for every mu in [0,2], including the logarithmic term and both degenerate endpoint partitions. With r=2/(2+mu), footrule=-2r^2+6r-5+1/r and xi=-4r^2+20r-17+2/r-1/r^2-12log(r). |
| Proposition 3.1: continuity and strict monotonicity | `Papers.Rockel2026XiFootrule.relaxed_coefficients_continuous`; `Papers.Rockel2026XiFootrule.relaxed_coefficients_strict_monotonicity` | verified | Continuous on the entire closed parameter interval; footrule strictly decreases and xi strictly increases. Derivative signs are proved on the interior, so zero endpoint derivatives cause no exception. |
| Proposition 3.1: endpoint values | `Papers.Rockel2026XiFootrule.relaxed_coefficients_endpoints` | verified | At mu=0 both coefficients are zero; at mu=2 footrule=-1/2 and xi=12log(2)-8. |
| Theorem 3.2: explicitly evaluated universal bound | `Papers.Rockel2026XiFootrule.weighted_lower_bound_closed` | verified | Every copula and mu in [0,2], using the exact rational and logarithmic formulas from Proposition 3.1. |
| Theorem 3.3: existence and uniqueness of the inverse parameter | `Papers.Rockel2026XiFootrule.footrule_inverse_unique` | verified | Every target footrule y in [-1/2,0] has exactly one matching mu in [0,2], including both endpoints. |
| Theorem 3.3: cubic equation and unique admissible root | `Papers.Rockel2026XiFootrule.footrule_cubic_equivalence`; `Papers.Rockel2026XiFootrule.footrule_cubic_unique_admissible` | verified | The prescribed footrule equation is equivalent to mu^3-(4+2y)mu^2-(4+8y)mu-8y=0 on [0,2]. Its root in that interval is unique for y in [-1/2,0]. |
| Theorem 3.3: nonpositive-footrule lower estimate | `Papers.Rockel2026XiFootrule.negative_footrule_lower_bound` | verified | Every copula with footrule in [-1/2,0] satisfies the explicit xi lower bound at its unique admissible cubic parameter. No copula-attainment assertion is added. |
| Theorem 3.3: correction to unrestricted real-root uniqueness | `Papers.Rockel2026XiFootrule.footrule_cubic_not_unique_real` | verified | At y=-1/2 the cubic has the distinct real roots 2 and -1. Thus the source's phrase "unique real solution" must be restricted to the admissible interval [0,2]. |
| Theorem 3.3: deterministic witnesses at xi=1 | `Papers.Rockel2026XiFootrule.rightBoundary_coefficients` | verified | A central W block of width a with identity outside has xi=1 and footrule=1-3a^2/2, for all a in [0,1]. The shared ordinal-sum construction proves it is a copula. |
| Theorem 3.3: entire xi=1 boundary | `Papers.Rockel2026XiFootrule.xi_one_slice` | verified | A pair (1,y) is attainable iff y lies in [-1/2,1]. The inverse width sqrt(2(1-y)/3) supplies an explicit witness, including both endpoints. |
| Theorem 3.3, equation (26): interval property and extension to xi=1 | `Papers.Rockel2026XiFootrule.fixed_footrule_intermediate`; `Papers.Rockel2026XiFootrule.fixed_footrule_upward` | verified | Every xi between two attained points at the same footrule is attained; every attained point extends to all xi up to 1 at the same footrule. No closed-slice or minimum-attainment assertion is included. |
| Theorem 3.3: convexity of the entire attainable region | `Papers.Rockel2026XiFootrule.attainable_region_convex` | verified | Any convex combination of two attainable coefficient pairs is attained by an actual copula. Independent two-mixture proof using the entire xi=1 boundary; no unproved lower-boundary formula, compactness, or closedness assumption. |
| Theorems 2.1 and 3.3: exact nonnegative-footrule part of the region | `Papers.Rockel2026XiFootrule.exact_nonnegative_footrule_region` | verified | For y>=0, (x,y) is attainable iff y<=1 and y^2<=x<=1. The Frechet witness attains the lower xi endpoint and fixed-footrule interpolation attains the full interval. |
| Theorem 3.3: continuity of footrule used in the closure proof | `Papers.Rockel2026XiFootrule.footrule_tendsto_of_cdf` | verified | Pointwise CDF convergence of arbitrary copulas implies convergence of footrule. Dominated convergence includes singular laws. |
| Theorem 3.3: closedness and compactness of the full region | `Papers.Rockel2026XiFootrule.attainable_region_closed`; `Papers.Rockel2026XiFootrule.attainable_region_compact` | verified | The entire attained region, including negative footrule. A weak copula limit, proved lower semicontinuity of xi, and fixed-footrule upward interpolation give an independent proof. |
| Theorem 3.3: boundary attainment in every slice | `Papers.Rockel2026XiFootrule.minimal_footrule_attained`; `Papers.Rockel2026XiFootrule.minimal_xi_attained` | verified | Every xi in [0,1] has a copula minimizing footrule; every footrule in [-1/2,1] has a copula minimizing xi. This is existence, not an explicit formula for the open negative boundary problem. |
| Theorem 3.3: cited SD compactness and rearrangement proof route | — | excluded | The actual closedness and attainment results above have an independent approximation and compactness proof. |
| Remark 2.6(c): lower-semilinear boundary witnesses | `Papers.Rockel2026XiFootrule.upperBoundary_isLowerSemilinear`; `Papers.Rockel2026XiFootrule.diagonalBoundary_isLowerSemilinear` | verified | Both boundary families have the standard representation min(u,v) q(max(u,v)), with q(t)/t nonincreasing on positive t. Includes all parameter endpoints. |
| Remark 2.6(c): universal lower-semilinear bound | `Papers.Rockel2026XiFootrule.lowerSemilinear_xi_le_footrule` | verified | Every lower-semilinear copula satisfies xi<=footrule; no SI hypothesis. A section Lipschitz bound gives the conditional-CDF square integral bound. |
| Remark 2.6(c): exact lower-semilinear region | `Papers.Rockel2026XiFootrule.exact_lowerSemilinear_xi_footrule_region`; `Papers.Rockel2026XiFootrule.lowerSemilinear_region_eq_si` | verified | A pair (x,y) is attained in the LSL class iff x,y lie in [0,1] and x<=y<=sqrt(x), exactly the SI region. Mixtures at fixed footrule remain LSL and fill the entire region. |
| Remark 2.6(d): printed matrix and rank values | `Papers.Rockel2026XiFootrule.printed_ltd_matrix`; `Papers.Rockel2026XiFootrule.printed_ltd_coefficients` | verified | The exact printed mass matrix defines a copula with xi=1/2 and footrule=1/3. The LTD assertion is false, as checked separately below. |
| Remark 2.6(d): formal counterexample to the printed LTD assertion | `Papers.Rockel2026XiFootrule.printed_ltd_claim_false` | verified | At (2/3,2/3), the printed checkerboard has CDF 5/12 < 4/9. It fails PQD, hence cannot be LTD. |
| Remark 2.6(d): corrected LTD counterexample | `Papers.Rockel2026XiFootrule.corrected_ltd_matrix`; `Papers.Rockel2026XiFootrule.corrected_ltd_counterexample`; `Papers.Rockel2026XiFootrule.corrected_ltd_not_si` | verified | Replacement mass matrix (1/9)*[[3,0,0],[0,1,2],[0,2,1]] is LTD on the full square, has xi=38/81 > 10/27=footrule, and is not SI. It proves the intended failure of xi<=footrule for LTD. |
| Remark 2.6(d): literal assertion that the printed matrix is LTD | — | excluded | False for the printed coefficients. The formal disproof and corrected witness above replace this assertion. |
| Remark 2.6(a),(e): open questions | — | excluded | The SI xi<=tau conjecture and explicit negative/SD boundary formulas are not claimed proved by the source. |
| Section 3.2, equation (31): actual pre-standardization marginals | `Papers.Rockel2026XiFootrule.twoParameter_raw_marginals`; `Papers.Rockel2026XiFootrule.twoParameter_marginal_density` | verified | The density outside the hole has uniform first marginal and second density (1-L(t))/(1-beta). Every alpha,beta in [0,1/2], including all edges. |
| Proposition 3.5, equation (32): actual copula density | `Papers.Rockel2026XiFootrule.twoParameter_density` | verified | Exact measure equality with the displayed quantile density on the closed parameter square. The proof handles flat marginal-CDF intervals through almost-everywhere quantile inversion; division by zero uses the zero version on null fibers. At alpha=1/2 the unused affine middle branch is replaced by the natural step-function extension. |
| Section 3.2: zero-width and checkerboard parameter endpoints | `Papers.Rockel2026XiFootrule.twoParameter_zero_width`; `Papers.Rockel2026XiFootrule.twoParameter_corner`; `Papers.Rockel2026XiFootrule.twoParameter_corner_coefficients` | verified | Every beta=0 copula is independence. The corner alpha=beta=1/2 is exactly the off-diagonal checkerboard of Theorem 3.4, with xi=1/2 and footrule=-1/2. |
| Equation (33): finite-parameter path and initial endpoint | `Papers.Rockel2026XiFootrule.twoParameter_path_admissible`; `Papers.Rockel2026XiFootrule.twoParameter_path_zero` | verified | The exact piecewise alpha(mu),beta(mu) lies in the proved parameter square for every finite mu>=0 and defines an actual copula; mu=0 is independence. Numerical boundary optimality is not asserted. |
| Equation (33) / resubmission Equation (38): continuous parameter path and limiting corner | `Papers.Rockel2026XiFootrule.twoParameter_parameters_continuous`; `Papers.Rockel2026XiFootrule.twoParameter_parameters_limit` | verified | The explicit alpha(mu),beta(mu) path is continuous, including the switch at mu=2, and tends to (1/2,1/2) at positive infinity. This row concerns the parameter path; it does not assert convergence of rank coefficients. |
| Table 2, Frechet row: exact coefficient formulas | `Papers.Rockel2026XiFootrule.frechet_coefficients` | verified | Xi=(a-b)^2+ab and footrule=a-b/2 over the full valid Frechet simplex, including all boundary parameters. The lower Frechet family has a=0. |
| Table 2, Frechet row: exact objective minimum | `Papers.Rockel2026XiFootrule.frechet_objective_lower` | verified | Xi+footrule>=-1/16 for the entire Frechet family. This is stronger than restriction to mixtures of W and independence, and is not asserted for arbitrary copulas. |
| Table 2, Frechet row: unique minimizing parameters | `Papers.Rockel2026XiFootrule.frechet_objective_eq_iff` | verified | Equality holds iff the M weight a=0 and W weight b=1/4. The independence weight is therefore 3/4; see the parameter correction below. |
| Table 2, Frechet row: exact attaining values | `Papers.Rockel2026XiFootrule.frechet_minimizer_coefficients` | verified | The actual copula (3/4)Pi+(1/4)W attains xi=1/16 and footrule=-1/8, hence sum=-1/16; no grid search or numerical integration. |
| Numerical optimization and plotted lower-bound candidates | — | excluded | Numerical evidence is not advertised as a Lean proof. |
| JCAM resubmission Proposition 3.4: strict mirrored relaxed bound | `Papers.Rockel2026XiFootrule.relaxed_mirrored_bound` | verified | Every mu in (0,2]; differentiate the exact squared defect and prove strict monotonicity, including the mu=2 endpoint. |
| JCAM resubmission Corollary 3.5: absolute bound and equality | `Papers.Rockel2026XiFootrule.negative_footrule_strict`; `Papers.Rockel2026XiFootrule.abs_footrule_le_sqrt_xi`; `Papers.Rockel2026XiFootrule.abs_footrule_eq_sqrt_xi_iff` | verified | Every copula satisfies abs(footrule)<=sqrt(xi). Equality iff the copula is a nonnegative Frechet mixture of Pi and M; strict for negative footrule. |
| JCAM resubmission Corollary 3.6: strict containment in xi-rho region | `Papers.Rockel2026XiFootrule.footrule_pair_attained_as_rho`; `Papers.Rockel2026XiFootrule.footrule_region_ssubset_rho_region` | verified | Construct a rho witness for each footrule pair using Frechet mixtures, reflection and fixed-rho interpolation. The pair (1,-1), attained by W for rho, proves strictness. |
| Journal/preprint correspondence | — | pending | Only the explicitly linked arXiv version is mapped. |

## Exact Frechet optimization and the Table 2 parameter convention

[FrechetMinimum.lean](FrechetMinimum.lean) proves the analytic Frechet row of
Table 2 exactly, and strengthens its minimum to the full Frechet simplex.
The minimizing copula is (3/4)Pi+(1/4)W, with xi=1/16 and footrule=-1/8.
The printed parameter 0.25 therefore denotes the W weight. In the prose
convention lambda*Pi+(1-lambda)*W, the corresponding parameter is lambda=3/4.
The other numerical table rows and plotted candidate boundaries remain
excluded from verified claims. This family minimum does not establish the
global negative-footrule boundary. The two-parameter construction is separately proved above.

## Two-parameter density and null fibers

[TwoParameter.lean](TwoParameter.lean) proves Proposition 3.5 from the actual
probability law with uniform density outside the exclusion band. Its first
marginal is uniform; its second marginal is atomless with the density in
equation (31). Applying that marginal's CDF gives a copula, and a proved
almost-everywhere quantile inverse identifies its density with equation (32).
This avoids assuming a strictly positive marginal density or differentiable
inverse. Density values on null fibers are immaterial to the measure, so the
proof does not claim the paper's pointwise marginal-density cancellation at
zero denominators. The finite-mu path is admissible; its numerical objective
values and suggested near-optimality remain numerical evidence.

## Closedness and attained slice extrema

[ClosedRegion.lean](ClosedRegion.lean) gives an independent proof of closedness.
Finite predictor-bin averages give lower xi approximations that converge to xi
for every copula and are continuous under pointwise CDF convergence. This proves
lower semicontinuity. A weakly convergent copula subsequence preserves uniform
marginals and footrule, and fixed-footrule interpolation raises xi to the desired
limit. Compactness then proves that every vertical and horizontal slice attains
its lower endpoint. No explicit negative-boundary formula is inferred.

## Correction to Remark 2.6(d)

The source's printed matrix `(1/12)*[[4,0,0],[0,1,3],[0,3,1]]`
has the advertised ranks but is not LTD. Its CDF at `(2/3,2/3)` is `5/12`,
which is strictly below `(2/3)*(2/3)=4/9`, contradicting the PQD condition
implied by LTD. This discrepancy is proved in Lean, not inferred from a plot.

The replacement `(1/9)*[[3,0,0],[0,1,2],[0,2,1]]` is proved LTD and has
`xi=38/81` and `footrule=10/27`, so it establishes the intended strict
counterexample. The proof checks the LTD inequality for all thresholds and
computes both coefficients exactly. The printed false LTD assertion is not
advertised as verified.

## Lower-semilinear region

[LowerSemilinearRegion.lean](LowerSemilinearRegion.lean) proves Remark 2.6(c).
The shared definition uses the usual diagonal representation: q(t)=delta(t)/t
for positive t, and q(t)/t=delta(t)/t^2 is nonincreasing. The value at zero
is immaterial. Copula margins and monotonicity supply the remaining diagonal
constraints. The proof bounds each conditional CDF by q(v), then integrates
its square to obtain xi<=footrule. This applies to LSL copulas without an SI
assumption. Both extremal families are LSL, and their mixtures at fixed footrule
attain every point between the two boundaries.
