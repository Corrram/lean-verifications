# Blest's rank correlation, compiled from its LaTeX source

`article.tex` is the article *Rank weighting and asymmetry in Blest's rank
correlation: two exact regions* (arXiv:2609.27634v1). It has a few local
edits, listed below. LeanMirror compiles this file in Lean; no separate formal
statement is written by hand.

| File | Role |
| --- | --- |
| `Compiled.lean` | `#mirror_article`. The kernel proves `compiled : compileArticle source = some doc` from the file's contents. This takes about 3 minutes. |
| `Article.lean` | `#mirror_semantics`. Every definition (`nu`, `rho`, `Phi`, `D`, …), claim (`claimK`) and definedness condition (`meaningfulK`) is stated as Lean, and kernel `rfl` theorems tie each one to `doc`. The command also generates the proof obligations `obligationK`. |
| `Steps.lean` | The proof of Corollary 3.2, sentence by sentence (claims 14–25), and its statement (claims 11–13), each derived from exactly the premises the text cites. This module imports only the compiled article and Mathlib. |
| `Bridge.lean` | Proved identifications of the article's definitions with the copula library and the companion development: `copulas_iff`, `rho_cdfOf`, `nu_cdfOf`, `survival_cdfOf`, `zeta_eq`, `D_eq`, `Phi_eq`, … |
| `Companion.lean` | The cited results (Theorem 1.1, Lemmas 2.2 and 3.1, the displayed formulas) and the well-definedness of all 15 definitions, proved through `Bridge`. |
| `Certified.lean` | `#mirror_certify`. The kernel checks `certificate`. The citation audit rejects any proof sentence whose justification uses a result it does not cite. The command exports `verifiedK : meaningfulK ∧ claimK` and writes `article.mirror.json`. |
| `article.mirror.json` | The per-sentence status read by the website reader (`lean-mirror/blest-spearman/compiled/`) and by `tex_diagnostics.py`. |

Current result: 26 claims are verified. 15 are derived in the text from their
citations, and 11 are checked by the companion development. All 15 definitions
are well defined, and the axioms are `propext`, `Classical.choice` and
`Quot.sound`. Four sentences do not compile yet, because they use `\Upsilon` or
`\Delta`, whose defining sentences the grammar does not read. They are reported
and assert nothing.

## Edits relative to arXiv v1

`article-edits.diff` is the exact diff. Each edit makes the text say precisely
what it means:

* `\CC` gets its own sentence ("let $\CC$ denote the class of bivariate
  copulas, that is, …"), and the citation moves to the next sentence.
* `\nu` and `\rho` are defined with `\coloneqq`, and Spearman's rho gets its own
  defining sentence ("For a copula $C$, Spearman's rho is …").
* The transpose $C^\top$ and the survival copula $\widehat C$ are defined in the
  introduction, before Theorem 1.1 uses the survival copula. The reflection
  $C^\perp$ gets its own defining sentence in Section 2.
* The text now defines "the copula associated with $\gamma$"
  ($(u,v)\mapsto\gamma(\{1-x\le u,\ 1-z\le v\})$) and $\gamma_T$ ("the law of
  $(X,T(X))$ for $X$ uniformly distributed on $[0,1]$").
* The phrase "supported on the graph of $f$" is now defined.
* Lemma 3.1 ends with "for every $c\in[0,1]$" (previously "for the function
  $\Phi$ in (4)"), and $D_c$ is introduced "For $c\in[0,1]$".
* Proof of Corollary 3.2:
  * "for every $r\in[-1,1]$" is added.
  * "By Lemma 3.1, $\rho(D_{1/2})=0$" replaces "Lemma 3.1 matches $r=0$ with $c=\frac12$".
  * "By (12), $\zeta_{1/2}(x)=|2x-1|$ …, so $D_{1/2}$ is supported on the graph of the tent map" replaces the change of coordinates.
  * "the map $C\mapsto\widehat C$ sends $\nu-\rho$ to $\rho-\nu$ by (8)" replaces "(8) sends".

## Check

```sh
lake build Papers.Rockel2026ExactBlest.Source.Certified
python .lake/packages/lean-mirror/scripts/tex_diagnostics.py Papers/Rockel2026ExactBlest/Source/article.mirror.json
```
