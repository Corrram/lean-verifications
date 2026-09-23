# Published-version comparison

The inspected final PDF is Marcus Rockel, *International Journal of Approximate
Reasoning* 197 (2026), 109744, DOI
[10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744).
Its SHA-256 is
`281d852284692cd23d311bbd104e502177b204d519ffd5eb819bd300ed3c315a`.
The primary result map in [COVERAGE.md](COVERAGE.md) retains the numbering of
[arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1).
The following final-PDF statements were compared directly with that map;
this is a selected statement-level comparison, not a claim that every line
of the published proof has been formalized.

| arXiv v1 map | Final IJAR PDF | Comparison |
| --- | --- | --- |
| Theorem 1.1 | Theorem 1 | The exact region, two coefficient branches, endpoint conventions, and unique curved-boundary family are covered by the mapped Lean results. |
| Lemmas 2.1-2.2; revised family proposition | Lemmas 1 and 3; Proposition 2.1 | Normalization, the actual copula and density, and the signed-family dependence properties are mapped. |
| Theorem 2.3 | Theorem 2 | Both exact coefficient branches and their joining point are proved. |
| Theorem 3.4 | Theorem 3 | The relaxed measurable-kernel optimum and almost-everywhere uniqueness are proved independently of the printed KKT route. |
| Lemma 4.3 | Lemma 5 | The final PDF prints the corrected decreasing concordance order for p >= p'; all four corrected shuffle claims are proved. |
| Lemma 4.4; Lemma 4.5 | Lemma 6; Lemma 7 | Mixture-path continuity and the derivative identity are proved. |
| Lemmas 4.1-4.2 | Lemmas 8-9 | Section moments, one-dimensional forms, and substitution regimes are mapped. |

Two **arXiv v1** intermediate statements are false, and the final IJAR PDF
corrects both. Its Lemma 5(iii), PDF p. 12, says `C_p <=_co C_p'` for
`p >= p'`; arXiv v1 Lemma 4.3(iii) had the direction reversed.
`shuffledCopula_concordance` proves the journal direction, while
`not_comonotonic_concordanceLE_countermonotonic` refutes the arXiv one.
The final PDF's Appendix A, p. 19, displays
`G_iv(r) = b^2(1/5 - 2r^2/3 + r^4 - 8r^5/15)`.
The coefficient `-8/15` agrees with `lower_square_polynomial`;
the arXiv v1 coefficient `-1/5` is refuted by
`printed_lower_square_polynomial_false`.
Neither correction should be attributed as an error in the final journal
article.

An earlier local author manuscript was inspected on 22 September 2026:
`xi-nu-region/ijar/xi-nu-region-ijar-rev2.tex` in the author's
`robust-portfolio-choices` checkout, SHA-256
`3d525cc0eb7ee7644bf6713addfa823161460fa83d1d830e791ba0cf6eeb215e`.
It adds the signed-family property proposition: positive-parameter MTP2,
negative-parameter SD, concordance ordering, and uniform limits at zero
and both infinities. `DensityTP2.lean`, `FamilyOrder.lean`, and
`UniformLimits.lean` prove those assertions for actual copulas. The
published PDF includes the corresponding signed-family proposition on
p. 6 (printed there as Proposition 2.1). `ShufflePath.lean` also
checks the endpoint-safe shuffle, which agrees almost everywhere with
the printed transformation at the split point.

The remaining in-progress status reflects the result-map scope and
source-proof obligations listed in [COVERAGE.md](COVERAGE.md); a selected
PDF comparison does not itself complete those obligations.