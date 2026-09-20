# Coverage

**Status: in progress.** The upper boundary in Theorem 2.1, its attainment and
unique equality case, and the sharp maximal gap are verified. The SI subregion
and the lower-bound results remain pending.

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

## Result map

All source references use arXiv v1. Proofs are in
[Definitions.lean](Definitions.lean) and [UpperBoundary.lean](UpperBoundary.lean).
[Axioms.lean](Axioms.lean) prints and enforces the transitive axiom allowlist.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (1): xi in the source derivative convention | `Papers.Rockel2026XiFootrule.xi_derivative_formula` | verified | Every bivariate copula; equality almost everywhere, with constant extension of CDF sections outside the unit interval. |
| Theorem 2.1: the Fréchet extremizer's CDF | `Papers.Rockel2026XiFootrule.cdf_upperBoundary` | verified | Entire closed square and parameter interval. |
| Theorem 2.1: universal bound, attainment, and unique maximizer | `Papers.Rockel2026XiFootrule.maximal_footrule` | verified | Every prescribed xi in [0,1]; all bivariate copulas, including singular copulas and both endpoints. |
| After Theorem 2.1 / Table 1: sharp upper bound on footrule minus xi | `Papers.Rockel2026XiFootrule.footrule_sub_xi_le` | verified | All bivariate copulas; the bound is 1/4. |
| After Theorem 2.1 / Table 1: unique equality case | `Papers.Rockel2026XiFootrule.footrule_sub_xi_eq_iff` | verified | Equality precisely at the half-independence, half-comonotonic mixture. |
| Lemmas A.1–A.2 and the paper's KKT proof strategy | — | excluded | The theorem above has an independent squared-distance proof. |
| Proposition 2.2 and Theorem 2.4: SI equality characterization and exact SI region | — | pending | Need the SI lower bound, its equality cases, and interior attainment. |
| Section 3.1: lower bounds and checkerboard minimum | — | pending | Need the piecewise integral formulas, optimization, and checkerboard comparison. |
| Section 3.2: two-parameter copula construction | — | pending | Need the marginal and parameter-endpoint proofs. |
| Numerical optimization and plotted lower-bound candidates | — | excluded | Numerical evidence is not advertised as a Lean proof. |
| Journal/preprint correspondence | — | pending | Only the explicitly linked arXiv version is mapped. |
