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
at the midpoint. The corrected full shuffling lemma remains pending; the
verified exact-region proof uses a different construction.

The local revision also explicitly states the almost-everywhere density
formula for the positive extremal copulas. The normalization inverse is now
proved differentiable at every interior response threshold, and its density
coefficient -b q'(v) is identified with the reciprocal active-band width. `DensityTP2.lean` establishes
existence of an MTP2 density for those copulas. The theorem
`extremal_standardized_density` gives an exact measure identity for the
standardized-band witness. The source switch points and the printed
-b q'(v) factor are checked, and that derivative expression agrees almost
everywhere with a measurable reciprocal-width candidate. The remaining
identity is between that candidate and the standardized-band witness. This is tracked as a separate
pending row in COVERAGE.md.

An earlier local author resubmission, `xi-nu-region-ijar-resubmission.tex`
(SHA-256 `fe9fc5291dd448672d92599c7913c09f30ad2f0ac540c53a68a7d80870556cb0`),
has the same 13 named result environments as the inspected rev2 file.
Five named statements have textual changes between those two local files;
the changes include formatting and inverse-hyperbolic-cosine notation in
the main region theorem. This comparison does not establish that either
local file matches the final publisher version.
