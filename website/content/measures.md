## Concordance and functional dependence

Two coefficients can summarize different aspects of the same distribution.
Keep the direction and normalization visible before comparing their values.
Throughout this chapter, $C$ is a bivariate copula and $(U,V)$ has law $C$.

## Spearman’s rho

Spearman’s population coefficient is the correlation of the uniform ranks:

$$\rho(C)=12\int_0^1\int_0^1 C(u,v)\,du\,dv-3.$$

It takes the values $-1,0,1$ at $W,\Pi,M$, respectively. It describes signed
concordance: reversing one coordinate reverses its sign.

## Chatterjee’s xi

For continuous margins, the copula formula in the direction “$V$ depends on $U$” is

$$\xi(C)=6\int_0^1\int_0^1 (\partial_1 C(u,v))^2\,du\,dv-2.$$

The partial derivative is interpreted almost everywhere. This is a directional
quantity; interchanging the coordinates can change it. In contrast to rho,
xi equals $1$ at both $M$ and $W$ and equals $0$ at $\Pi$.

The formulas and direction used here follow equations (1) and (3) of
[Ansari & Rockel, arXiv:2506.15897v3](https://arxiv.org/html/2506.15897v3).
Matching derivative formulas to the library’s conditional-distribution
representation is a separate formalization task.

## Other coefficients in the collection

The following formulas fix the conventions used in the handbook. They are
mathematical reference formulas, not claims that the corresponding article
statements have already been formalized.

| Coefficient | Copula formula |
| --- | --- |
| Kendall’s tau | $\tau(C)=4\int_{[0,1]^2}C(u,v)\,d\mu_C(u,v)-1$ |
| Spearman’s footrule | $\phi(C)=6\int_0^1 C(t,t)\,dt-2$ |
| Blomqvist’s beta | $\beta(C)=4C(\tfrac12,\tfrac12)-1$ |
| Gini’s gamma | $\gamma(C)=4\int_0^1(C(t,t)+C(t,1-t))\,dt-2$ |

Notice the measure in the tau integral: it is $\mu_C$, not planar Lebesgue
measure. Footrule and gamma instead evaluate the CDF along diagonals, while
beta evaluates it at a single point.

The [dependence-family article](https://arxiv.org/html/2310.17307v3) provides
the surrounding conventions. For Blest’s coefficient, consult the
[xi–Blest supplement](site:papers/Rockel2026XiBlest/) and its versioned source;
the directional convention must be matched explicitly.

## A minimal consistency check

Before translating a longer calculation, evaluate the definition at $\Pi$,
$M$, and $W$. This catches sign, scaling, and coordinate mistakes early.
Such a check does not prove a formula for an entire copula family; a verified
family formula must retain its full parameter domain and endpoint cases.
