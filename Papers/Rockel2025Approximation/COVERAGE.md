# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

Source: [arXiv:2505.08045v2](https://arxiv.org/abs/2505.08045v2), 22 May 2026.

Planned scope: Association formulas for approximating copulas and checkerboard approximation results under the source hypotheses.
The verified scope is currently empty.

## Initial roadmap

This initial roadmap follows the arXiv v2 abstract; exact result numbering is pending. Do not transfer the broader convergence wording from v1 without checking the revised hypotheses.

| Source target (v2) | Lean declaration | Status | Work needed |
| --- | --- | --- | --- |
| Approximation constructions | — | pending | Specify the Bernstein, shuffle, checkerboard, and check-min representations. |
| Association formulas | — | pending | Derive the relevant coefficient formulas with exact grid and parameter conventions. |
| Checkerboard bounds and convergence | — | pending | Preserve the absolute-continuity and TP2-density assumptions stated in v2. |

Replace broad targets with individual numbered results as work proceeds.
Every `verified` row needs a checked declaration, explicit hypotheses, and an
axiom report in [Axioms.lean](Axioms.lean). Pending targets belong in this map,
not in incomplete Lean declarations.

## Source correspondence

Record normalization choices, direction conventions, parameter endpoints, and
any additional hypotheses before claiming a source result is covered.
Generic copula lemmas should be reused from or contributed to the upstream
library; this folder records their precise application to this article.
