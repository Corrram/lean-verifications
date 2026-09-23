# Published-version comparison

The inspected final PDF is Marcus Rockel, *Journal of Computational and
Applied Mathematics* 485 (2026), 117466, DOI
[10.1016/j.cam.2026.117466](https://doi.org/10.1016/j.cam.2026.117466).
Its SHA-256 is
`5dcbfb0d113c4e2ccc731b337f9dd37a02eb789b91189872fd0c5cfaf641ff6e`.
The primary result map in [COVERAGE.md](COVERAGE.md) retains the numbering of
[arXiv:2509.07232v1](https://arxiv.org/abs/2509.07232v1).
The following final-PDF results were compared directly; full
statement-by-statement correspondence remains in progress.

| arXiv v1 map | Final JCAM PDF | Comparison |
| --- | --- | --- |
| Theorem 2.1 | Theorem 2.1 | Upper bound and unique extremizer are checked. |
| Proposition 2.2 | Proposition 1 | SI equality implications are checked; the arbitrary-interval ordinal-sum converse in final Remark 1 remains pending. |
| Theorem 2.4; Corollary 2.5 | Theorem 2.2; Corollary 1 | Exact SI region and Kendall consequence are checked. |
| Remark 2.6(d) | Remark 2(d) | The final PDF uses the corrected LTD matrix and exact ranks, proved in `LTDExample.lean`. |
| Theorem 3.2 | Theorem 3.1 | Universal relaxed lower estimate is checked. |
| Theorem 3.3 | Theorem 3.2 | Convexity, closedness, slices and the inverse lower estimate on the admissible interval are checked; see the false unrestricted-root phrase below. |
| Proposition 3.1 | Proposition 2 | Closed relaxed coefficient formulas are checked. |
| Additional resubmission results | Proposition 3; Corollaries 2-3 | Strict mirrored estimate, absolute square-root bound and strict region containment are checked. |
| Theorem 3.4; Proposition 3.5 | Theorem 3.3; Proposition 4 | Unique checkerboard minimum and actual two-parameter copula density are checked. |

The final JCAM PDF, p. 7, **corrects the arXiv v1 LTD example**.
Remark 2(d) prints `(1/9)*[[3,0,0],[0,1,2],[0,2,1]]` with
`xi=38/81 > 10/27=footrule` and states that this copula is LTD.
`corrected_ltd_matrix` and `corrected_ltd_counterexample` verify
those claims. The old arXiv v1 matrix
`(1/12)*[[4,0,0],[0,1,3],[0,3,1]]` is not LTD, as
`printed_ltd_claim_false` proves. The website's discrepancy notice
therefore identifies **arXiv v1**, not the published article.

The final JCAM PDF, p. 10, **retains one false phrase** in Theorem 3.2:
it calls `mu(y)` the `unique real solution` of
`mu^3 - (4+2y)mu^2 - (4+8y)mu - 8y = 0`.
At `y=-1/2`, both `mu=2` and `mu=-1` are real roots. Lean proves
this with `footrule_cubic_not_unique_real`. The theorem's proof later
specifies a unique solution in the admissible interval `[0,2]`,
which is the corrected statement proved by
`footrule_cubic_unique_admissible`. The literal unrestricted
uniqueness claim is excluded, and no exact negative-footrule
attainment is inferred from the relaxed bound.

The earlier local resubmission
`xi-footrule/jcam/xi-footrule-region-jcam_resubmission.tex`
(SHA-256 `0b824be25f6231602b90add3d3421a67f78be311e6ebfb69b189bb153a57758b`)
was inspected on 22 September 2026. Its numbering differs from the
final PDF, so the table above uses the published numbering. For
adjacent countable ordinal sums, the Lean supplement proves SI,
exchangeability and rank equality componentwise, including Pi/M
blocks. It does not prove the published Remark 1 converse over
arbitrary nonadjacent intervals and a residual comonotonic part.