# Additional author manuscript

Inspected locally on 22 September 2026:

- File: `xi-nu-region/ijar/xi-nu-region-ijar-rev2.tex` in the author's `robust-portfolio-choices` checkout.
- SHA-256: `3d525cc0eb7ee7644bf6713addfa823161460fa83d1d830e791ba0cf6eeb215e`.
- Title: The exact region between Chatterjee's and Blest's rank correlations.

The revised manuscript adds Proposition `prop:basic_properties_cb`, including
MTP2 for positive parameters, SD for negative parameters, concordance ordering
across signed parameters, and uniform copula limits at zero and both infinities.
The arXiv map already checks SI, reflection of coefficients, coefficient limits,
and a cofinal uniform CDF limit. Those results alone do not prove all parts of
this additional proposition. Its remaining assertions are tracked explicitly
in COVERAGE.md. This manuscript has not been identified with the publisher's
final version; final journal comparison remains pending.

FamilyOrder.lean and UniformLimits.lean now verify the full signed CDF order,
negative-parameter SD and all three uniform copula limits. DensityTP2.lean also verifies the MTP2 density assertion via an actual
standardized band law, completing this additional proposition. Final published
text correspondence remains pending.

## Comparison with arXiv v1 and earlier local revision

The arXiv v1 statement of Lemma 4.3(iii) says that, for p >= p', the
shuffled copulas satisfy C_p >=_co C_p'. The local author revision reverses
this inequality. With C=M, the printed endpoint transformations give C_0=M
and C_1=W, so arXiv v1 would imply M <=_co W. The Lean theorem
`not_comonotonic_concordanceLE_countermonotonic` disproves that consequence
at the midpoint. The endpoint-safe transformation in ShufflePath.lean differs from the printed
map only at the null split point. Lean proves that it preserves the uniform
marginal, yields an actual copula for every p, and has the two stated endpoint
copulas. It also proves xi invariance for arbitrary copulas, the corrected
concordance direction for SI copulas, and uniform CDF continuity via the
pointwise bound 2 abs(p-p'). Thus all four claims of the local revision's
shuffling lemma are checked. The exact-region proof also has an independent
construction.

The local revision also explicitly states the almost-everywhere density
formula for the positive extremal copulas. The normalization inverse is
proved differentiable at every interior response threshold, and its density
coefficient -b q'(v) is identified with the reciprocal active-band width.
The raw-band marginal quantile has intercept -b q(v), its column density
is (b+1) times the active width, and its closed support strip agrees almost
everywhere with the revision's open switching interval. The theorem
`extremal_toMeasure_derivativeDensity` identifies the displayed
derivative-form expression with the actual copula measure for every b>0.
Together with `extremal_hasMTP2Density`, this verifies the revised lemma's
density formula and the revised proposition's MTP2 assertion. The exact
published text correspondence remains pending.

An earlier local author resubmission, `xi-nu-region-ijar-resubmission.tex`
(SHA-256 `fe9fc5291dd448672d92599c7913c09f30ad2f0ac540c53a68a7d80870556cb0`),
has the same 13 named result environments as the inspected rev2 file.
Five named statements have textual changes between those two local files;
the changes include formatting and inverse-hyperbolic-cosine notation in
the main region theorem. This comparison does not establish that either
local file matches the final publisher version.
