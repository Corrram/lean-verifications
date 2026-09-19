# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

Source: [arXiv:2606.30033v1](https://arxiv.org/abs/2606.30033v1), 29 June 2026.

Planned scope: The xi-beta region, the two-strip boundary family, attainment, and selected subclasses.
The verified scope is currently empty.

## Initial roadmap

This initial roadmap follows the arXiv abstract; exact result numbering is pending. Check the continuity argument for mixtures and keep directional xi conventions explicit.

| Source target (v1) | Lean declaration | Status | Work needed |
| --- | --- | --- | --- |
| Two-strip family | — | pending | Construct the copulas and derive their coefficient formulas. |
| Sharp boundary bounds | — | pending | Prove the region inequalities and boundary attainment. |
| Interior and subclasses | — | pending | Establish attainability and record which subclass claims are included. |

Replace broad targets with individual numbered results as work proceeds.
Every `verified` row needs a checked declaration, explicit hypotheses, and an
axiom report in [Axioms.lean](Axioms.lean). Pending targets belong in this map,
not in incomplete Lean declarations.

## Source correspondence

Record normalization choices, direction conventions, parameter endpoints, and
any additional hypotheses before claiming a source result is covered.
Generic copula lemmas should be reused from or contributed to the upstream
library; this folder records their precise application to this article.
