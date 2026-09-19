# Coverage

**Status: scaffold.** No article result is claimed verified yet.

## Source and scope

Source: [arXiv:2506.15897v3](https://arxiv.org/abs/2506.15897v3), 19 May 2026.
Journal reference: [DOI 10.1016/j.jmva.2026.105630](https://doi.org/10.1016/j.jmva.2026.105630); version comparison pending.

Planned scope: Exact xi-rho region, diagonal-band extremizers, and the inequality under stochastic monotonicity.
The verified scope is currently empty.

## Initial roadmap

The roadmap uses the theorem numbering in arXiv v3. Prove the correspondence between the paper's derivative formulas and the library's conditional-distribution definitions. Keep the direction of stochastic monotonicity explicit.

| Source target (v3) | Lean declaration | Status | Work needed |
| --- | --- | --- | --- |
| Theorem 1 | — | pending | Exact region, boundary attainment, and uniqueness; build the diagonal-band family first. |
| Corollary 1 | — | pending | Sharp maximum of rho minus xi, including its equality case. |
| Theorem 2 | — | pending | Inequality for stochastically increasing or decreasing copulas and equality cases. |

Replace broad targets with individual numbered results as work proceeds.
Every `verified` row needs a checked declaration, explicit hypotheses, and an
axiom report in [Axioms.lean](Axioms.lean). Pending targets belong in this map,
not in incomplete Lean declarations.

## Source correspondence

Record normalization choices, direction conventions, parameter endpoints, and
any additional hypotheses before claiming a source result is covered.
Generic copula lemmas should be reused from or contributed to the upstream
library; this folder records their precise application to this article.
