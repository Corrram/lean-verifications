# Spearman's rho and Gini's gamma, compiled from the LaTeX source

`article.tex` is the article *The exact region determined by Spearman's rho and
Gini's gamma* (arXiv:2609.19890v1), with the local edits listed below.
[Proofread](https://github.com/Corrram/proofread) compiles this file in Lean;
no separate formal statement is written by hand. This is the second article
compiled this way, after `Papers/Rockel2026ExactBlest/Source`. Its main
statements are verified through the existing development of the paper in this
folder's parent.

| File | Role |
| --- | --- |
| `Compiled.lean` | `#proofread_article`: the kernel compiles `article.tex`. |
| `Article.lean` | `#proofread_semantics`: `rho`, `gamma`, `Omegarhogamma` (`Ω_{ρ,γ}`), `rhoBar` (`ρ̄(g) = max{ρ(C) : C ∈ 𝒞, γ(C) = g}`, a definite description), the constants `dStar`, `gStar`, `d0`, `Delta0`, `r0`, `g0`, and the claims `claimK` with their definedness conditions. |
| `Bridge.lean` | `ρ` and `γ` are `spearmanRho` and `giniGamma` of the copula library, `Ω_{ρ,γ}` is `region`, `ρ̄` is `upperRho`, and the radical constants are the development's. |
| `Proofs.lean` | Proofs of every compiled claim (Theorem 1.1: the region, its shape, the shape and endpoints of `ρ̄`; Corollaries 2.1 and 2.4, Proposition 2.3) and every definition's well-definedness. |
| `Certified.lean` | `#proofread_certify`: the certificate, `verifiedK`, and the reports. |

## Coverage

The certificate (`Certified.lean`) and `article.proofread.json` give the following coverage.

| Sentences | compiled | not compiled | prose | total |
| --- | ---: | ---: | ---: | ---: |
| text | 5 | 1 | 178 | 184 |
| results | 9 | 3 | 53 | 65 |
| proofs | 0 | 5 | 166 | 171 |
| all | 14 | 9 | 397 | 420 |

* **Definitions.** 11 definitions, each with a proof that it is well defined.
* **Claims.** 8 claims (8 in statements of results, 0 proof steps, 0 in the running text), 8 verified: 8 proved through the bridges from the companion development.
* **Not compiled.** 9 sentences use a construction the grammar does not read yet. They assert nothing checked:
  * line 201 (theorem): undefined symbol: G
  * line 425 (text): undefined symbol: \delta
  * line 594 (remark): undefined symbol: G
  * line 740 (lemma): undefined symbol: \mathsf
  * line 804 (proof): unsupported construction: '
  * line 1003 (proof): undefined symbol: y
  * line 1010 (proof): undefined symbol: a
  * line 1018 (proof): undefined symbol: x
  * line 1145 (proof): undefined symbol: t
* **Results with sentences that are prose.** These sentences are shown in the reader but assert nothing checked:
  * theorem at line 192 (`thm:main`): 3 of 6 sentences compiled
  * corollary at line 514 (`cor:elementary`): 1 of 4 sentences compiled
  * proposition at line 603 (`prop:discrepancy`): 2 of 3 sentences compiled
  * corollary at line 631 (`cor:signs`): 2 of 4 sentences compiled
  * lemma at line 663 (`lem:representations`): 0 of 4 sentences compiled
  * lemma at line 703 (`lem:sign-attainment`): 0 of 1 sentences compiled
  * lemma at line 738 (`lem:duality`): 1 of 5 sentences compiled
  * lemma at line 771 (`lem:input`): 0 of 1 sentences compiled
  * lemma at line 813 (`lem:halfshift-range`): 0 of 1 sentences compiled
  * lemma at line 838 (`lem:parameter-checks`): 0 of 1 sentences compiled
  * definition at line 874 (`def:extremizers`): 0 of 6 sentences compiled
  * proposition at line 894 (`prop:moments`): 0 of 1 sentences compiled
  * example at line 915 (`ex:map`): 0 of 7 sentences compiled
  * lemma at line 988 (`lem:extension`): 0 of 2 sentences compiled
  * theorem at line 1032 (`thm:support`): 0 of 4 sentences compiled
* **Axioms.** `propext`, `Classical.choice`, `Quot.sound`.

## Edits relative to arXiv v1

`article-edits.diff` is the exact diff. Each edit makes the text say precisely
what it means, and none changes the mathematics:

* The coefficients are defined by their integral formulas with `\coloneqq`
  ("For a copula $C$, Spearman's rho and Gini's gamma are …"), followed by the
  moment representations, instead of the reverse order.
* The region `Ω_{ρ,γ}` is defined after the coefficients it uses ("The exact
  region between Spearman's rho and Gini's gamma is …").
* `ρ̄` gets a defining sentence with its domain ("For $g\in[-1,1]$, set
  $\overline\rho(g)\coloneqq\max\{\dots\}$").
* The constants `d_*`, `g_*`, `d_0`, `Δ_0`, `r_0`, `g_0` are defined with
  `\coloneqq`, and their decimal values are written with `\approx`.
* In Corollary 2.4 the image sets name the class of their variable
  (`\{\rho(C):C\in\CC,\ \gamma(C)=0\}`).
* Theorem 1.1 states the region equation in its own sentence ("It holds that
  …"), names the region by its symbol ("Moreover, $\Omega_{\rho,\gamma}$ is
  compact, convex and centrally symmetric, …"), and writes the endpoint values as
  "$\overline\rho(-1)=-1$ and $\overline\rho(1)=1$".

## Check

```sh
lake build Papers.AnsariRockelSteinmassl2026RhoGamma.Source.Certified
lake exe proofread check Papers/AnsariRockelSteinmassl2026RhoGamma/Source/article.tex --vocab unitsquare --claims
```
