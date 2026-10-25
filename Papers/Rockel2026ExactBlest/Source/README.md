# Blest's rank correlation, compiled from its LaTeX source

`article.tex` is the article *Rank weighting and asymmetry in Blest's rank
correlation: two exact regions* (arXiv:2609.27634v1), with the local edits
listed below. [Proofread](https://github.com/Corrram/proofread) compiles this
file in Lean: its definitions, statements and proof sentences, as written. No
separate formal statement is written by hand.

| File | Role |
| --- | --- |
| `Compiled.lean` | `#proofread_article`. The kernel proves `compiled : compileArticle vocab source = some doc` from the file's contents, with the core vocabulary and the vocabulary of probability on the unit square. `LexCache/` holds the lexing certificates of the article's sections (written by `proofread prepare`), so that an edit relexes only its own section. |
| `Article.lean` | `#proofread_semantics`. Every definition (`nu`, `rho`, `Phi`, `Upsilon`, `D`, `A`, `B`, `Lambda`, …), claim (`claimK`) and definedness condition (`meaningfulK`, `wellDefinedI`) is stated as Lean, and kernel `rfl` theorems tie each one to `doc`. The command also generates the proof obligations `obligationK`. |
| `Steps.lean` | The proof of Corollary 3.2, sentence by sentence (claims 17–28), and its statement (claims 14–16), each derived from exactly the premises the text cites. This module imports only the compiled article and Mathlib. |
| `Bridge.lean`, `Families.lean` | Proved identifications of the article's definitions with the copula library and the companion development: `copulas_iff`, `rho_cdfOf`, `nu_cdfOf`, `eta_cdfOf`, `D_eq`, `A_eq`, `B_eq`, `B_half`, `Phi_eq`, `Upsilon_eq`, `Lambda_eq`, …. The generic part (copulas of the vocabulary are library copulas) is `Papers/Common/UnitSquareCopula.lean`. |
| `Companion.lean`, `CompanionFamilies.lean` | The results the article states without a compiled proof (Theorems 1.1 and 1.2, Lemmas 2.2, 3.1 and 4.1, Corollaries 4.5 and 4.6, the displayed formulas) and the well-definedness of all definitions, proved through the bridges. |
| `Potentials.lean`, `Dual.lean` | The cost `d_κ`, the parameters `κ_w`, `κ_b` and the potentials `φ_w, ψ_w, φ_b, ψ_b` of Section 4.2, which the article defines by a value and a piecewise derivative (read as `φ(x) = φ(a) + ∫_a^x φ'`), are the companion's potentials, by the fundamental theorem of calculus on each piece (`Papers/Common/Calculus.lean`). `Dual.lean` proves Propositions 4.3 and 4.4 from them. |
| `Certified.lean` | `#proofread_certify`. The kernel checks `certificate`. The citation audit rejects any proof sentence whose justification uses a result it does not cite. The command exports `verifiedK : meaningfulK ∧ claimK` and writes `article.proofread.json` and `article.proofread.tex`. |
| `article.proofread.json` | The per-sentence status read by the website reader (`…/compiled/`) and by `proofread_diagnostics.py`. |

## Coverage

The certificate (`Certified.lean`) and `article.proofread.json` give the following coverage.

| Sentences | compiled | not compiled | prose | total |
| --- | ---: | ---: | ---: | ---: |
| text | 25 | 0 | 134 | 159 |
| results | 23 | 0 | 25 | 48 |
| proofs | 6 | 5 | 133 | 144 |
| all | 54 | 5 | 292 | 351 |

* **Definitions.** 37 definitions, each with a proof that it is well defined.
* **Claims.** 47 claims (28 in statements of results, 12 proof steps, 7 in the running text), 47 verified: 15 derived in the text from the premises they cite (checked by the citation audit), 32 proved through the bridges from the companion development.
* **Not compiled.** 5 sentences use a construction the grammar does not read yet. They assert nothing checked:
  * line 346 (proof): undefined symbol: \sup
  * line 659 (proof): unsupported construction
  * line 691 (proof): undefined symbol: \Delta
  * line 697 (proof): undefined symbol: \Delta
  * line 757 (proof): unsupported construction
* **Results with sentences that are prose.** These sentences are shown in the reader but assert nothing checked:
  * lemma at line 258 (`lem:coupling`): 0 of 2 sentences compiled
  * lemma at line 341 (`lem:rearrangement`): 0 of 2 sentences compiled
  * lemma at line 597 (`lem:dual-certificate`): 0 of 6 sentences compiled
  * corollary at line 874 (`cor:asymmetry`): 2 of 3 sentences compiled
  * corollary at line 922 (`cor:nu-transpose`): 2 of 4 sentences compiled
* **Axioms.** `propext`, `Classical.choice`, `Quot.sound`.

## Edits relative to arXiv v1

`article-edits.diff` is the exact diff. Each edit makes the text say precisely
what it means, and none changes the mathematics:

* `\CC` gets its own sentence ("let $\CC$ denote the class of bivariate
  copulas, that is, …"), and the citation moves to the next sentence.
* `\nu` and `\rho` are defined with `\coloneqq`, and Spearman's rho gets its own
  defining sentence ("For a copula $C$, Spearman's rho is …").
* The transpose $C^\top$ and the survival copula $\widehat C$ are defined in the
  introduction, before Theorem 1.1 uses the survival copula. The reflection
  $C^\perp$ gets its own defining sentence in Section 2.
* The text defines "the copula associated with $\gamma$", $\gamma_T$ and
  $\gamma^T$ ("the law of $(T(Z),Z)$ for $Z$ uniformly distributed on
  $[0,1]$") in separate sentences.
* The phrase "supported on the graph of $f$" is defined.
* The parametrization $e_b$ of $\Upsilon$ states its parameter range.
* Lemma 3.1 ends with "for every $c\in[0,1]$" (previously "for the function
  $\Phi$ in (4)"), and $D_c$ is introduced "For $c\in[0,1]$".
* Section 4.1 introduces each family in its own sentence with its parameter
  domain ("For $w\in[0,1]$, let $A_w$ be …, where $T_w:[0,1]\to[0,1]$ is given
  by …"; "For $b\in(0,\frac12]$, set $z_b\coloneqq…$ and let $B_b$ be …").
* The branches `z_∓` of Section 4.1 get their own defining sentence ("For
  $b\in(0,\frac12]$, set (15)"), followed by the sentence about the conditional
  law, which used to carry the definitions in its display.
* The support `S_w` of Section 4.2 names its parameter ("For $w\in[\frac12,1)$,
  the support of $\gamma_{T_w}$ is …"), and the pieces `R_b^∓` are defined in a
  sentence of their own ("Set $R_b^-(z)\coloneqq…$ and $R_b^+(z)\coloneqq…$.").
* Corollary 4.5 separates "Both constants are sharp." from the extremizer
  statement.
* Proof of Corollary 3.2: "for every $r\in[-1,1]$" is added; "By Lemma 3.1,
  $\rho(D_{1/2})=0$" replaces "Lemma 3.1 matches $r=0$ with $c=\frac12$"; "By
  (12), $\zeta_{1/2}(x)=|2x-1|$ …, so $D_{1/2}$ is supported on the graph of the
  tent map" replaces the change of coordinates; "the map $C\mapsto\widehat C$
  sends $\nu-\rho$ to $\rho-\nu$ by (8)" replaces "(8) sends".

## Check

```sh
lake build Papers.Rockel2026ExactBlest.Source.Certified
python .lake/packages/proofread/scripts/proofread_diagnostics.py Papers/Rockel2026ExactBlest/Source/article.proofread.json --prose
lake exe proofread check Papers/Rockel2026ExactBlest/Source/article.tex --vocab unitsquare --claims
```
