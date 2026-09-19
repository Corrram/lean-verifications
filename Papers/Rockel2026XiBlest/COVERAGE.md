# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

Source: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
Journal reference: [DOI 10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744); version comparison pending.

Planned scope: The xi-Blest region, its extremal copula family, coefficient formulas, and constrained optimization argument.
The verified scope is currently empty.

## Initial roadmap

This initial roadmap follows the arXiv abstract; exact result numbering is pending. Review the weighting convention for Blest's coefficient and all optimization hypotheses.

| Source target (v1) | Lean declaration | Status | Work needed |
| --- | --- | --- | --- |
| Definitions and optimization | — | pending | Define Blest's coefficient with the paper's convention and state the optimization constraints. |
| Extremal family | — | pending | Construct the family and prove its coefficient formulas. |
| Exact region | — | pending | Prove the bounds, attainment, and stated uniqueness. |

Replace broad targets with individual numbered results as work proceeds.
Every `verified` row needs a checked declaration, explicit hypotheses, and an
axiom report in [Axioms.lean](Axioms.lean). Pending targets belong in this map,
not in incomplete Lean declarations.

## Source correspondence

Record normalization choices, direction conventions, parameter endpoints, and
any additional hypotheses before claiming a source result is covered.
Generic copula lemmas should be reused from or contributed to the upstream
library; this folder records their precise application to this article.
