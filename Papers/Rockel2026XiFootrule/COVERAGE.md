# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

Source: [arXiv:2509.07232v1](https://arxiv.org/abs/2509.07232v1), 8 September 2025.
Journal reference: [DOI 10.1016/j.cam.2026.117466](https://doi.org/10.1016/j.cam.2026.117466); version comparison pending.

Planned scope: Upper boundary and equality cases, the stochastically increasing subregion, and lower bounds for the xi-footrule region.
The verified scope is currently empty.

## Initial roadmap

This initial roadmap follows the arXiv abstract; exact result numbering is pending. The title must not be taken as a claim that the general lower boundary has already been determined.

| Source target (v1) | Lean declaration | Status | Work needed |
| --- | --- | --- | --- |
| Upper boundary | — | pending | Construct the extremal Frechet copulas and prove the equality characterization. |
| Stochastically increasing subclass | — | pending | Establish both inequalities and attainment throughout the stated subregion. |
| Lower-bound results | — | pending | Separate proved bounds and copula constructions from a claim of an exact lower boundary. |

Replace broad targets with individual numbered results as work proceeds.
Every `verified` row needs a checked declaration, explicit hypotheses, and an
axiom report in [Axioms.lean](Axioms.lean). Pending targets belong in this map,
not in incomplete Lean declarations.

## Source correspondence

Record normalization choices, direction conventions, parameter endpoints, and
any additional hypotheses before claiming a source result is covered.
Generic copula lemmas should be reused from or contributed to the upstream
library; this folder records their precise application to this article.
