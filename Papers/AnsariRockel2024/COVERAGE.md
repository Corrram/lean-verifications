# Coverage

**Status: in progress.** Selected results from Tables 5 and 6 are checked on
their full stated parameter domains. This is not a verification of all 38
families or of the entire article.

## Source and conventions

Source: [arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3).
Correspondence with the [journal version](https://doi.org/10.1515/demo-2024-0002)
remains pending.

A copula is represented by its probability measure. The classical
representation theorem below proves existence and uniqueness from the
classical boundary and rectangle conditions. The FGM CDF is checked explicitly.
Fréchet uses weights $a$ on $M$, $b$ on $W$, and $1-a-b$ on independence,
with $a,b\geq0$ and $a+b\leq1$. Mardia uses
$a=\theta^2(1+\theta)/2$ and $b=\theta^2(1-\theta)/2$.
Signed parameters satisfy $-1\leq\theta\leq1$; singular endpoints are included.
CI and CD mean conditional monotonicity in both directions. Rho and tau
use the source population normalizations; xi is coordinate 1 given coordinate 0.

The library defines xi using a regular conditional CDF. The bridge to the
source's almost-everywhere partial derivative is proved in
[ConditionalDerivative.lean](https://github.com/Corrram/copula/blob/5d7fba65b37e50b86194e0a9938f42513e4403be/Copula/Rank/ConditionalDerivative.lean),
without assuming an absolutely continuous copula.

## Result map

Every row refers to arXiv v3. Each named declaration is compiled, printed,
and checked against the standard axiom allowlist in [Axioms.lean](Axioms.lean).

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Section 2.1: classical representation | `Papers.AnsariRockel2024.classical_representation` | verified | Bivariate classical boundary and rectangle conditions; unique representing measure. |
| Table 5: FGM CDF | `Papers.AnsariRockel2024.fgm_cdf` | verified | Entire closed square and signed parameter interval. |
| Section 2.4: derivative formula for xi | `Papers.AnsariRockel2024.xi_derivative_formula` | verified | All bivariate copulas; almost-everywhere correspondence with the conditional CDF. |
| Table 6, FGM, Spearman rho | `Papers.AnsariRockel2024.fgm_rho` | verified | Full signed interval, including zero and both endpoints. |
| Table 6, FGM, Kendall tau | `Papers.AnsariRockel2024.fgm_tau` | verified | Full signed interval, including zero and both endpoints. |
| Table 6, FGM, Chatterjee xi | `Papers.AnsariRockel2024.fgm_xi` | verified | Full signed interval, including zero and both endpoints. |
| Table 6, Frechet, Spearman rho | `Papers.AnsariRockel2024.frechet_rho` | verified | Full weight simplex, including singular endpoints. |
| Table 6, Frechet, Kendall tau | `Papers.AnsariRockel2024.frechet_tau` | verified | Full weight simplex, including singular endpoints. |
| Table 6, Frechet, Chatterjee xi | `Papers.AnsariRockel2024.frechet_xi` | verified | Full weight simplex, including singular endpoints. |
| Table 6, Mardia, Spearman rho | `Papers.AnsariRockel2024.mardia_rho` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Table 6, Mardia, Kendall tau | `Papers.AnsariRockel2024.mardia_tau` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Table 6, Mardia, Chatterjee xi | `Papers.AnsariRockel2024.mardia_xi` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Table 5 / Appendix A.4.1: FGM CI | `Papers.AnsariRockel2024.fgm_ci` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.1: FGM CD | `Papers.AnsariRockel2024.fgm_cd` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.2: FGM lower orthant order | `Papers.AnsariRockel2024.fgm_lowerOrthant` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.3: FGM lower and upper tails | `Papers.AnsariRockel2024.fgm_tails` | verified | Full signed interval, including zero and both endpoints. |
| Table 5 / Appendix A.4.3: Frechet tails | `Papers.AnsariRockel2024.frechet_tails` | verified | Full weight simplex, including singular endpoints. |
| Table 5 / Appendix A.4.3: Mardia tails | `Papers.AnsariRockel2024.mardia_tails` | verified | Full signed interval; nonnegative W-weight as specified above. |
| Remaining family constructors and table entries | — | pending | Unlisted cells are not covered by the results above. |
| General dependence/order equivalences and their applications | — | pending | Density TP2 and rearrangement-based Schur order need separate correspondence checks. |
| Journal/preprint correspondence | — | pending | Only the explicitly linked arXiv version is mapped. |

Proof sources: [Definitions.lean](Definitions.lean),
[Association.lean](Association.lean), and [Dependence.lean](Dependence.lean).

## Source discrepancies and exclusions

The Fréchet simplex and Mardia W-weight above follow the valid copula
mixtures. The reversed simplex inequality and negative W-weight printed in
Appendix A.4.1 / equation (23) are not asserted as theorems. Table 6's
coefficient formulas are checked with the valid family definitions.

Other discrepancies documented in the pinned library's
[coverage audit](https://github.com/Corrram/copula/blob/5d7fba65b37e50b86194e0a9938f42513e4403be/docs/ansari-rockel.md)
remain outside this verified subset. Numerical plots, grid searches, and
numerical-only table observations are excluded from the formal claims.
