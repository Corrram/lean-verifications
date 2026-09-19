# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

The initial roadmap uses [arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3).
The publication is identified by [DOI 10.1515/demo-2024-0002](https://doi.org/10.1515/demo-2024-0002).
Matching its numbering and content to the journal version is pending.

Planned work covers dependence and ordering properties, and formulas for
association measures. This scope must be refined into individual theorem and
table-entry rows before it can be called complete. The verified scope is
currently empty.

## Starting points

The pinned upstream
[coverage index](https://github.com/Corrram/copula/blob/f3594c079d205f717fc17a6563e7200251d37f30/docs/ansari-rockel.md)
records candidate library results and remaining gaps. Check the exact
declarations and hypotheses before transferring a claim into the result map.

| Area in arXiv v3 | Candidate upstream modules | Next step |
| --- | --- | --- |
| Section 2: definitions and conventions | `Copula.Basic`, `Copula.Classical`, `Copula.Dependence`, `Copula.Order`, `Copula.Rank` | Prove or document the correspondence of representations and conventions |
| Section 3.1 and family tables: dependence and ordering | Modules under `Copula.Families`, plus `Copula.Order` and `Copula.Dependence` | Map each result and parameter domain separately |
| Section 3.2 and Appendix A.5: association measures | `Copula.Rank` and family-specific modules | Match formulas and endpoint cases to exact declarations |
| Appendix computations and tail entries | `Copula.TailDependence` and family-specific modules | Separate proved claims, pending claims, and numerical observations |

These are planning areas, not verified result rows.

## Result map

| Source result and version | Lean declaration / file | Status | Hypotheses, conventions, or gaps |
| --- | --- | --- | --- |

Use `pending`, `verified`, or `excluded` for individual rows. Keep pending
statements here rather than adding incomplete Lean declarations. A `verified`
row needs a checked declaration, a reviewed match to the source statement, and
an axiom report in `Axioms.lean`. Document additional hypotheses explicitly.

## Differences from the article

Review CI versus one-direction SI, density TP2 versus CDF TP2, the direction
of Schur comparison, singular copulas, and endpoint conventions. These are
highlighted in the upstream index and need explicit treatment when matching
article statements. No equivalence or correction is asserted by this scaffold.

Numerical figures and observations are outside the initial proof scope unless
a later coverage entry gives an exact mathematical statement and a proof.
