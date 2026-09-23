# Publisher and arXiv comparison

The source used for theorem statements and numbering in this supplement remains
[arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3).
I also inspected the open-access [published PDF](https://www.degruyterbrill.com/document/doi/10.1515/demo-2024-0002/pdf)
of *Dependence Modeling* 12 (2024), article 20240002, DOI
[10.1515/demo-2024-0002](https://doi.org/10.1515/demo-2024-0002).
The publisher PDF has 36 pages; the mapped arXiv v3 PDF has 33. The
following is a statement-level comparison of the rows already checked, not a
certificate that every table cell in either version has been verified.

| Result or discrepancy | Published location | Comparison |
| --- | --- | --- |
| Lemma 2.6, monotone-class Schur/lower-orthant implications | p. 7 (PDF index 6) | Same two-part statement and hypotheses as arXiv v3. |
| Lemma 2.8, conditionally decreasing analogue | p. 8 (PDF index 7) | Same two-part statement and reversed orthant direction. |
| Proposition 3.2, survival invariance | p. 10 (PDF index 9) | Same three numbered clauses. |
| Theorem 3.4, extreme-value orders | p. 14 (PDF index 13) | Same five equivalences, including the still-unproved general CI premise used for the Schur directions. |
| Table 6 and Appendix A.5 | pp. 18 and 31–34 (PDF indices 17 and 30–33) | The same named family rows and Marshall–Olkin/Cuadras–Augé calculation sections appear. Formula-by-formula correspondence for unverified cells remains pending. |
| Fréchet mixture condition | Appendix A.4.1, p. 30 (PDF index 29) | The printed condition still says `α + β ≥ 1`, opposite to the valid mixture simplex `α + β ≤ 1`. |
| Mardia W coefficient | Appendix A.4.1, equation (A7), p. 30 (PDF index 29) | The published expression retains the negative W coefficient identified in arXiv equation (23). The formalization uses the nonnegative coefficient of the actual copula mixture. |
| Fréchet parameter order | Appendix A.4.2, p. 31 (PDF index 30) | The published text still says the family increases when either weight is increased; the W-weight direction fails for the valid mixture. |
| Mardia CI/CD and density TP2 | Appendix A.4.1, p. 30 (PDF index 29) | The published text still omits the independence case `θ = 0` from CI/CD and labels singular endpoints TP2 under a density interpretation. The Lean correction remains necessary. |

The published text therefore does not resolve these printed discrepancies.
Other family cells and all uninspected differences between the two versions
remain outside this comparison. The article stays in progress.

## arXiv v3 Nelsen 7 xi intermediate expression

[Appendix A.5.1 of arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3)
prints `6 ∫∫ (θv+1−θ)^2 (θuv+(1−θ)(u+v−1))₊ du dv − 2` as an
intermediate expression for Nelsen 7's xi. `nelsen7_printed_xi_candidate_expanded`
identifies this expression with the CDF-weighted integral. `nelsen7_printed_xi_candidate_formula` proves that it equals
−1−θ/4 for every parameter, while `nelsen7_xi` proves the actual value
is 1−θ. The interior witness `nelsen7_printed_xi_identity_false_half`
compares −9/8 with 1/2 at θ=1/2, inside the parameter range of the
appendix calculation. `nelsen7_printed_xi_identity_false` refutes the
intermediate equality throughout the closed parameter interval. The final Table 6 identity xi=1−θ is correct and
verified independently from the actual conditional CDF. This comparison
is pinned to arXiv v3; it does not assert that the journal version contains
the same intermediate error.

## arXiv v3 AMH lower-tail endpoint

[Table 3 of arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3)
prints lower-tail coefficient zero for the Ali–Mikhail–Haq family without
excluding θ=1. The Lean theorems `amh_tails_lt_one` and `amh_tails_one`
prove the pair (0,0) for −1≤θ<1 and (1/2,0) at θ=1. The endpoint copula
is Clayton(1), so the printed zero at that endpoint is false. This finding
is pinned to arXiv v3; the corresponding journal table cell has not been
compared.
