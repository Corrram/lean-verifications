## What does an exact region mean?

Given two real-valued functionals $a$ and $b$ on a class $\mathcal C$ of copulas,
their attainable region is

$$\mathcal R_{a,b}=\{(a(C),b(C)):C\in\mathcal C\}.$$

An inequality gives an outer constraint. An exact description additionally
requires attainment: every point in the proposed set must come from an
admissible copula. A boundary formula alone does not settle the interior.

## The proof obligations

An article’s region theorem typically separates into several tasks:

1. **Universal bounds.** Show that each admissible copula produces a point in the proposed set.
2. **Extremal construction.** Define copulas attaining boundary values, and prove that they have uniform margins.
3. **Attainment throughout.** Construct a copula for every remaining point in the set.
4. **Equality cases.** State and prove any uniqueness claim with all exceptional and endpoint cases.

For three coefficients, the same logic applies in $\mathbb R^3$. Sections
at a fixed coefficient can organize the argument, but their compatibility
still needs proof.

## A guide to the xi–rho article

The [xi–rho supplement](site:papers/AnsariRockel2026XiRho/) tracks three
targets from arXiv v3: the attainable region (Theorem 1), the sharp maximum
of $\rho-\xi$ (Corollary 1), and the inequality under stochastic monotonicity
(Theorem 2). Theorem 2 is now verified in full, including all equality
cases. The curved region boundary, full interior attainment, and sharp
global gap remain pending; the entire xi=1 boundary is verified.

The paper proves $\xi(C)\leq|\rho(C)|$ for the stated stochastically increasing
or decreasing classes. Keeping this class restriction attached to the
inequality is essential. The verification proves that equality holds exactly
at countermonotonicity, independence, or comonotonicity, without a density
assumption. The supporting scalar Lemma 8 is checked with equality of
functions interpreted almost everywhere.
See [the versioned article](https://arxiv.org/html/2506.15897v3) for the exact
statements and equality cases.

## Equality in the SI xi–footrule region

The [xi–footrule supplement](site:papers/Rockel2026XiFootrule/) verifies the
entire SI region and Proposition 2.2's full equality criterion for its lower
boundary. Equality holds precisely when the conditional CDF has the source's
three-level representation with measurable, nondecreasing cut functions.
Both directions and the derivative convention are checked, including singular
copulas. Theorem 3.2's universal Jensen lower bound is also checked in exact
integral form, with the piecewise scalar optimizer and its uniqueness proof.
The relaxed family is not an attaining copula family: a formal counterexample
shows that its primitive fails CDF monotonicity. Closed coefficient formulas,
remaining region geometry, and copula constructions retain their pending
entries in the coverage map.

## A picture is a guide, not a coverage claim

Plots and numerical optimizers can suggest extremizers. A machine-checked
region statement still needs exact definitions and quantified proofs of the
inclusions above. A finite sample of attainable points cannot establish
attainment of a continuum.

Mixtures require care too. Even if copulas form a convex class, a coefficient
may be nonlinear in the copula. A straight segment in coefficient space does
not follow merely by mixing two copulas.

## Find the corresponding supplement

| Coefficients or topic | Article folder |
| --- | --- |
| $\xi,\rho$ | [Ansari & Rockel](site:papers/AnsariRockel2026XiRho/) |
| $\xi,\phi$ | [Rockel: xi–footrule](site:papers/Rockel2026XiFootrule/) |
| $\xi$, Blest | [Rockel: xi–Blest](site:papers/Rockel2026XiBlest/) |
| $\xi,\beta$ | [Orenday Lares & Rockel](site:papers/OrendayLaresRockel2026XiBeta/) |
| $\tau,\phi,\beta$ | [Orenday Lares & Rockel](site:papers/OrendayLaresRockel2026TauFootruleBeta/) |
| $\rho,\phi$ | [Ansari & Rockel](site:papers/AnsariRockel2026RhoFootrule/) |
| $\rho,\gamma$ | [Ansari, Rockel & Steinmaßl](site:papers/AnsariRockelSteinmassl2026RhoGamma/) |
| Approximation | [Rockel: approximating copulas](site:papers/Rockel2025Approximation/) |

Read each coverage map for its actual scope. In particular, an article title
containing “exact region” is not a claim that its full result is verified here.
