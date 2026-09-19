## A joint distribution with uniform margins

Take a random pair $(U,V)$ whose two coordinates are uniform on $[0,1]$.
Its law $\mu_C$ is a bivariate copula measure. The associated distribution function is

$$C(u,v)=\mathbb{P}(U\leq u,\ V\leq v)=\mu_C([0,u]\times[0,v]).$$

These are two representations of one object. An article often starts with $C$;
the Lean library starts with the probability measure and derives its CDF.
The distinction matters whenever an argument integrates against the copula itself.

## The formal representation

[`ProbabilityTheory.Copula`](site:api/Copula/Basic.html#ProbabilityTheory.Copula)
stores a probability measure on `Fin d → I`, with a proof that every coordinate
has the uniform law. Here `I` is mathlib’s unit interval. The bivariate case has
dimension `2`.

```lean
-- The library's mathematical object:
ProbabilityTheory.Copula 2
```

The [CDF module](site:api/Copula/CDF.html) connects this representation to
distribution functions. Two useful starting points are
[`cdf_nonneg`](site:api/Copula/CDF.html#ProbabilityTheory.Copula.cdf_nonneg)
and [`cdf_one`](site:api/Copula/CDF.html#ProbabilityTheory.Copula.cdf_one).
Their documentation displays the precise types and hypotheses.

## Three reference copulas

The classical examples provide quick normalization checks:

| Copula | Distribution function | Interpretation |
| --- | --- | --- |
| $\Pi$ | $\Pi(u,v)=uv$ | Independent coordinates |
| $M$ | $M(u,v)=\min(u,v)$ | The law of $(U,U)$ |
| $W$ | $W(u,v)=\max(u+v-1,0)$ | The law of $(U,1-U)$ |

For every bivariate copula, the Fréchet–Hoeffding inequalities read

$$W(u,v)\leq C(u,v)\leq M(u,v).$$

These examples also expose a common trap: $M$ and $W$ are concentrated on
lines and have no two-dimensional density. A density-based argument needs
its own hypotheses; it cannot silently cover every copula.

## Fix the convention before proving the statement

A formalization should say which coordinate is conditioned on, whether a
derivative is understood almost everywhere, and which measure is used in each
integral. Endpoint parameters and singular limits deserve explicit treatment.

For the dependence-family article, also distinguish conditional increase in
both directions from a one-direction stochastic monotonicity assumption, and
total positivity of a density from total positivity of a CDF. The
[2024 supplement](site:papers/AnsariRockel2024/) records these correspondence
questions before any article result is marked verified.

For the paper’s conventions and family tables, see
[Ansari & Rockel, arXiv:2310.17307v3](https://arxiv.org/html/2310.17307v3).
The generated reference documents the imported portion of the pinned
[copula library](https://github.com/Corrram/copula), alongside the paper modules.
