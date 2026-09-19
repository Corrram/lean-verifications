# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

Source: [arXiv:2608.20176v1](https://arxiv.org/abs/2608.20176v1), 20 August 2026.

Planned scope: The rho-footrule region and optimal transport proof, with applications tracked separately.
The verified scope is currently empty.

## Initial roadmap

This initial roadmap follows the arXiv abstract; exact result numbering is pending. Formalize the transport feasibility and duality conditions before using them to conclude global optimality.

| Source target (v1) | Lean declaration | Status | Work needed |
| --- | --- | --- | --- |
| Transport formulation | — | pending | Prove the reduction and construct matching primal and dual objects. |
| Exact region | — | pending | Establish optimality, attainment, and the stated uniqueness. |
| Applications | — | pending | Track finite rankings, mixability, and Chatterjee-related consequences individually. |

Replace broad targets with individual numbered results as work proceeds.
Every `verified` row needs a checked declaration, explicit hypotheses, and an
axiom report in [Axioms.lean](Axioms.lean). Pending targets belong in this map,
not in incomplete Lean declarations.

## Source correspondence

Record normalization choices, direction conventions, parameter endpoints, and
any additional hypotheses before claiming a source result is covered.
Generic copula lemmas should be reused from or contributed to the upstream
library; this folder records their precise application to this article.
