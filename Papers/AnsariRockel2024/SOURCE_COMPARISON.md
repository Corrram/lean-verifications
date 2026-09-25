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
| Theorem 3.4, extreme-value orders | p. 14 (PDF index 13) | Same five equivalences. The general CI theorem is now proved from max-stability, so the audited copula-form Schur equivalences no longer require an independent CI premise. |
| Table 6 and Appendix A.5 | pp. 18 and 31–34 (PDF indices 17 and 30–33) | The same named family rows and Marshall–Olkin/Cuadras–Augé calculation sections appear. Formula-by-formula correspondence for unverified cells remains pending. |
| Fréchet mixture condition | Appendix A.4.1, p. 30 (PDF index 29) | The printed condition still says `α + β ≥ 1`, opposite to the valid mixture simplex `α + β ≤ 1`. |
| Mardia W coefficient | Appendix A.4.1, equation (A7), p. 30 (PDF index 29) | The published expression retains the negative W coefficient identified in arXiv equation (23). The formalization uses the nonnegative coefficient of the actual copula mixture. |
| Fréchet parameter order | Appendix A.4.2, p. 31 (PDF index 30) | The published text still says the family increases when either weight is increased; the W-weight direction fails for the valid mixture. |
| Mardia CI/CD and density TP2 | Appendix A.4.1, p. 30 (PDF index 29) | The published text still omits the independence case `θ = 0` from CI/CD and labels singular endpoints TP2 under a density interpretation. The Lean correction remains necessary. |
| Plackett CI/CD and TP2 | Appendix A.4.1, p. 30 (PDF index 29) | The journal retains CI iff theta>=1, CD iff theta<=1, the TP2 exclusion for theta>2, and only numerical evidence for TP2 on [1,2]. The audited `plackett_density_tp2_iff` now proves that exact closed range. |
| Raftery density exclusion | Appendix A.4.1, p. 30 (PDF index 29) | The journal repeats the assertion that no parameter has a density. `raftery_absolutelyContinuous_iff` and `raftery_density_tp2_iff` refute it: both properties hold exactly for delta<1. |
| Raftery CI and lower-orthant order | Appendix A.4.1–A.4.2, pp. 30–31 (PDF indices 29–30) | The published CI and increasing lower-orthant statements agree with the audited `raftery_ci` and `raftery_lowerOrthant_monotone`. |

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

## arXiv v3 Tawn TP2 exclusion

[Table 5 of arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3) labels non-independent Tawn copulas as non-TP2. The admitted parameter range includes both weights equal to one, which Table 4 identifies with Gumbel. `tawn_one_one_density_tp2` verifies an actual TP2 density throughout this subfamily. `tawn_one_one_not_independence` proves non-independence for shape greater than one using the positive upper tail. `tawn_printed_tp2_exclusion_false` refutes the universal exclusion with shape two and unit weights. This does not classify the other Tawn weights. The corresponding journal table cell has not yet been compared.


## arXiv v3 Plackett decreasing Schur range

[Table 5 of arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3) prints the decreasing Schur range as theta<=0, while Table 4 admits only theta>0. This leaves the decreasing range empty. The Lean theorem `plackett_schur_below_one` proves both directional Schur comparisons throughout 0<theta<=eta<=1, using the exact CD classification and the independently proved lower-orthant order. `plackett_schur_above_one` verifies the increasing range above independence. We record the useful decreasing range (0,1] as a correction, rather than treating the vacuous printed condition as coverage of that range. The corresponding journal cell has not been compared.

## arXiv v3 Plackett Spearman rho

[Table 6 of arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3) prints
`(theta+1)/(theta-1) - 2*(2*theta/(theta-1)^2)*log(theta)`.
The Lean theorem `plackett_spearmanRho` derives the corrected expression
`(theta+1)/(theta-1) - 2*theta*log(theta)/(theta-1)^2` by integrating the
actual copula CDF. The odds equation gives a section antiderivative;
the fundamental theorem of calculus and Fubini give the full integral.
`plackett_spearmanRho_one` supplies the independence value zero.
`plackett_printed_rho_false` refutes the printed expression at theta=2.
This comparison is pinned to arXiv v3; the corresponding journal cell
has not been compared.

## arXiv v3 Raftery formula and endpoints

[Table 1 of arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3)
prints the Raftery CDF with coefficient `1-delta`. The exact Lean
counterexample `raftery_printed_cdf_not_copula` shows that this expression
cannot be a copula CDF: at delta=1/2 and u=v=7/8 its value is
5985/8192, strictly below the necessary lower bound u+v-1=3/4.
The literal formula therefore cannot be used as the family constructor.

Appendix A.4.1 says that no Raftery parameter has a density, although
Table 4 identifies delta=0 with independence. `raftery_zero_density`
checks that this endpoint identity implies a TP2 Lebesgue density.
Table 5 prints upper-tail coefficient zero without excluding delta=1,
which Table 4 identifies with comonotonicity. `raftery_one_upperTail`
checks that this endpoint has coefficient one and cannot have coefficient
zero. Both endpoint results state the endpoint identity as a hypothesis;
they are endpoint consistency checks. The subsequent theorem `raftery_cdf`
now constructs an actual copula measure and verifies the full-square
formula with coefficient `(1-delta)/(1+delta)` for delta<1. Its mixture
representation proves uniform margins and nonnegative rectangle
increments; `raftery_zero` and `raftery_one` verify both endpoint identities.
The actual tail limits are now checked by `raftery_tails_lt_one` and
`raftery_tails_one`: lower=2*delta/(1+delta), upper=0 for delta<1, and
both coefficients equal one at delta=1. Full-square parameter continuity
and both endpoint limits are also checked. `raftery_spearmanRho` now
verifies the printed Table 6 rho formula for the corrected family by
integrating the actual mixture CDF, including both endpoints. The density calculation now gives a stronger correction: the actual
measure is absolutely continuous and has TP2 density exactly for delta<1.
The first and mixed CDF derivatives agree across the diagonal, and
interior-rectangle integration identifies the density. Its factorization
into coordinate weights and an antitone function of max(u,v) proves TP2.
`raftery_printed_tp2_exclusion_false` gives a non-independent delta=1/2
counterexample to Table 5. CI/PQD hold throughout [0,1]; CD/NQD hold only
at independence. Increasing lower-orthant and both-direction Schur
parameter orders are also verified on the entire closed interval.
`raftery_kendallTau` verifies the printed Table 6 formula
`2*delta/(3-delta)` for the corrected family, including both endpoints.
Integration of the actual CDF against its identified density gives
`(4*a-1)/(4*(2*a+1))`, where `a=1/(1-delta)` in the interior.
Symmetry reduces the calculation to one triangle, where the inner
integral is a linear combination of three powers.
The journal's Appendix A.4.1 density exclusion, CI assertion, and A.4.2
lower-orthant assertion have now been compared above. The corresponding
journal table formulas and tail cells remain to be checked. This distinction
is intentional: publisher PDF text was available for the prose comparison,
but page rendering and a direct PDF download failed during this check.

## Gaussian xi: arXiv v3 discrepancy and proved correction

The [arXiv v3 PDF, page 19](https://arxiv.org/pdf/2310.17307v3#page=19) and [HTML Table 6](https://arxiv.org/html/2310.17307v3) both print the arcsine argument `1/2 + r^2/(1+r)`. The checked theorem `gaussian_printed_xi_argument_outside_domain` shows it exceeds one for every `-1<r<-1/2`; `gaussian_printed_xi_argument_counterexample` evaluates it to `11/4` at `r=-3/4`. The correlation-matrix theorem confirms these are admissible parameters of the actual Gaussian family. This is a failure of the classical real arcsine domain, independent of any totalized library convention outside [-1,1]. The corrected xi formula is proved below; the journal version of this cell remains unchecked.

The stronger theorem `gaussian_printed_xi_formula_false` now refutes the literal formula on the actual signed Gaussian family without using out-of-domain arguments. At `r=-1/2` the expression equals one; at `r=1/2` it is strictly less than one. The proved Gaussian sign-reflection identity implies equal actual xi values at these two correlations. The printed arguments are respectively one and two-thirds, both within the classical real arcsine domain. The corrected general formula is now proved below; journal correspondence remains pending.

The theorem `gaussian_chatterjeeXi` proves the corrected expression
`(3/pi)*arcsin((1+r^2)/2)-1/2` for the actual Gaussian copula on the full
closed interval `[-1,1]`. The proof identifies its actual conditional CDF,
represents its squared integral using four independent standard normals,
and checks that the resulting normalized Gaussian pair has correlation
`(1+r^2)/2`. Its lower-quadrant probability yields the formula. The singular
endpoints use the checked benchmark copulas. This is a derived correction,
not a claim that the printed arXiv v3 cell agrees with it.

## Elliptical endpoint qualifications

The [arXiv v3 HTML Appendix A.3.3](https://arxiv.org/html/2310.17307v3#A3.SS3) assigns Gaussian tail coefficient one to both signed singular endpoints. The checked Gaussian family equals W at r=-1, where both coefficients are zero. The declarations `gaussian_negative_one_not_lowerTail_one` and `gaussian_negative_one_not_upperTail_one` formally refute coefficient one by uniqueness of the tail limits. The positive endpoint has both coefficients one. This passage has not been checked against the journal version; the cached journal PDF is empty and cannot serve as evidence.

Table 2 includes Student-t correlation r=1 in the admissible range and identifies that member as M. The scale-mixture construction now proves this identity for every real nu>0, and `student_one_isCI` verifies CI there. Thus the blanket not-CI language in Table 5 and Appendix A.3.1 needs an interior-parameter qualification. The interior non-CI claim is now proved for every real nu>0. The exact full-range results are `student_isCI_iff` (CI exactly at r=1), `student_isCD_iff` (CD exactly at r=-1), and `student_not_hasMTP2Density` (no density-TP2 member).

The negative Student-t endpoint is now also proved: `student_negative_one` identifies it with W for every real nu>0, and `student_negative_one_isCD` proves CD there. Thus the closed parameter range includes both CI and CD singular members. The common marginal-law identity is verified independently of correlation; the analytic marginal and joint densities are now checked, and the interior SI/CI and SD/CD exclusions are now proved from the actual conditional CDF. A continuous version violates antitonicity at threshold 3*sqrt(nu), and equivalence of the marginal with Lebesgue measure rules out repair on a null set. Reflection supplies the SD/CD exclusion.

## Student-t density: arXiv v3 HTML dimension-symbol discrepancy

[arXiv v3 HTML Table 1](https://arxiv.org/html/2310.17307v3) prints correlation `rho` in the dimension slots of the Student-t density: `Gamma((nu+rho)/2)`, `nu^(rho/2)`, `pi^(rho/2)`, and power `-(nu+rho)/2`. The formal definition `Verification.studentPrintedJointPDF` transcribes that literal expression with the bivariate correlation determinant and quadratic form. At correlation zero, degrees of freedom two, and the origin, it equals one. The actual standard density proved from the Gaussian-gamma construction equals `1/(2*pi)` there, strictly below one. The public theorem `student_joint_printed_formula_false` refutes the universal pointwise identity. A single-point counterexample is not used to claim inequality of measures.

The checked correction is the standard dimension-two formula in `student_joint_standard_density`: the power is `-(nu+2)/2`, and the gamma recurrence simplifies the normalizing factor to `1/(2*pi*sqrt(1-rho^2))`. This comparison was checked against the arXiv v3 HTML. The arXiv PDF and journal wording of this particular cell remain unchecked.
