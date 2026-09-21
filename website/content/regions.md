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
global gap remain pending; the entire xi=1 boundary and full-region convexity are verified.

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
copulas. Theorem 3.2's universal Jensen lower bound is checked with the
piecewise scalar optimizer and its uniqueness proof. Proposition 3.1 now
provides exact rational and logarithmic coefficient formulas, continuity,
strict monotonicity, and both endpoint values.

For target footrule in [-1/2,0], the inverse parameter exists uniquely in
[0,2] and satisfies the source's cubic. This gives the explicit xi lower
estimate in Theorem 3.3 on that range. The interval restriction is essential:
at footrule -1/2 the cubic also has the inadmissible real root -1, besides 2.
The coverage map records this correction to the source's global uniqueness
wording. The relaxed profile also fails copula monotonicity, so no copula
attainment is asserted for this estimate. Remaining region geometry and
copula constructions retain their pending entries.

## Convexity in three xi regions

The xi-footrule, xi-rho, and xi-Blest supplements now verify convexity of
their full attainable regions. The proof constructs a copula for every
convex combination of two attained pairs: first mix the given copulas,
then mix with a xi=1 witness at the same second coefficient to reach the
desired xi. The continuous xi path and affine second coefficient justify
both steps. Closedness and the remaining curved-boundary formulas are
separate obligations.

For xi-footrule, the entire xi=1 boundary is now checked as well. Centered
countermonotonic blocks give every footrule value in [-1/2,1]. Together
with the Frechet lower-xi endpoint at nonnegative footrule, these witnesses
prove the exact portion 0<=footrule<=1 and footrule^2<=xi<=1, including
attainment throughout. At negative footrule, the proved Jensen bound
remains an outer estimate; convexity does not make it an attaining curve.

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
