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
