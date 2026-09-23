# Source comparison

The primary public numbering remains arXiv:2509.07232v1. An additional author
manuscript was inspected locally on 22 September 2026:

- File: `xi-footrule/jcam/xi-footrule-region-jcam_resubmission.tex` in the author's `robust-portfolio-choices` checkout.
- SHA-256: `0b824be25f6231602b90add3d3421a67f78be311e6ebfb69b189bb153a57758b`.
- Identity: title and author match the cited article. This is a journal resubmission, not evidence of the final published text.

## Numbering and additional results

| arXiv v1 | JCAM resubmission | Coverage |
| --- | --- | --- |
| Theorem 2.1 | Theorem 2.1 | Upper bound and unique extremizer checked. |
| Proposition 2.2 | Proposition 2.2 | Full SI equality characterization checked. |
| Theorem 2.4, Corollary 2.5 | Same | Exact SI region and Kendall consequence checked. |
| Proposition 3.1 | Proposition 3.3 | Closed relaxed coefficients checked. |
| Theorem 3.2 | Theorem 3.1 | Universal relaxed lower estimate checked. |
| Theorem 3.3 | Theorem 3.2 | Convexity, compactness, slices and admissible inverse checked. |
| Absent | Proposition 3.4 | Strict mirrored relaxed bound checked in AbsoluteBound.lean. |
| Absent | Corollary 3.5 | Absolute square-root bound and equality cases checked. |
| Absent | Corollary 3.6 | Strict region containment checked with actual witnesses. |
| Theorem 3.4 | Theorem 3.7 | Unique checkerboard minimum checked. |
| Proposition 3.5 | Proposition 3.8 | Actual two-parameter copula density checked. |

The resubmission's Remark 2.6(d) uses the corrected matrix
`(1/9)*[[3,0,0],[0,1,2],[0,2,1]]` and ranks `38/81` and `10/27`, already
proved in LTDExample.lean. The formal disproof in the arXiv coverage concerns
the older printed matrix only.

Finite nested ordinal sums of independence and comonotonic blocks are proved
SI and symmetric with xi=footrule, and interior binary sums of SI components satisfy
an equality iff criterion. The general countable ordinal-sum classification
remains open in this supplement. Adjacent countable Pi sums are proved symmetric
and decomposable at every partition endpoint, with first component Pi.
The recursive tail decomposition proves xi=footrule equality for this adjacent countable family. The pinned copula package proves its SI property by CDF-section interpolation. The arbitrary-block extension in CountableOrdinalGeneral.lean proves rank equality for adjacent countable sums whenever each block has it, and SI plus exchangeability for Pi/M blocks. CountableOrdinalSI.lean further proves that an adjacent countable sum is SI exactly when each component is SI. Neither result proves the source’s converse classification over arbitrary nonadjacent intervals.
The source's explicit parameter path continuity and limiting parameter endpoint
are checked in ParameterPath.lean. Final publisher correspondence remains pending;
this local comparison does not mark the published article complete.
