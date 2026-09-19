# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

Source: [arXiv:2609.19890v1](https://arxiv.org/abs/2609.19890v1), 17 September 2026.

Planned scope: The rho-gamma region, its boundary constructions, and the optimal transport argument.
The verified scope is currently empty.

## Initial roadmap

This initial roadmap follows the arXiv abstract; exact result numbering is pending. Verify the interfaces between boundary pieces and the accumulation limit.

| Source target (v1) | Lean declaration | Status | Work needed |
| --- | --- | --- | --- |
| Boundary parametrization | — | pending | Define the parameter intervals, junction, and limiting cases. |
| Global optimality | — | pending | Build the transport construction and verify the matching dual potential. |
| Consequences | — | pending | Track maximal separation and sign thresholds as distinct results. |

Replace broad targets with individual numbered results as work proceeds.
Every `verified` row needs a checked declaration, explicit hypotheses, and an
axiom report in [Axioms.lean](Axioms.lean). Pending targets belong in this map,
not in incomplete Lean declarations.

## Source correspondence

Record normalization choices, direction conventions, parameter endpoints, and
any additional hypotheses before claiming a source result is covered.
Generic copula lemmas should be reused from or contributed to the upstream
library; this folder records their precise application to this article.
