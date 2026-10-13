# LeanMirror mathematical companions

[LeanMirror](https://github.com/Corrram/lean-mirror) supplies a reusable language
for precise mathematical statements, their interpretation in Lean, and their
readable presentation. This repository consumes the exact Git commit pinned in
`lakefile.toml` and `lake-manifest.json`.

The main reader reproduces the **complete original article** from
[arXiv:2609.27634v1](https://arxiv.org/abs/2609.27634v1), preserving its order,
wording, numbered formulas, result environments, proofs, figures, captions, and
bibliography. Coefficients link to their original definitions. Every labeled
result has links to compiled mathematical counterparts; drawers show their
actual Lean types and lead to the generated API. This is a source-preserving
reader with evidence overlays. It does **not** yet certify every literal passage
of the original proofs; its visible coverage count records that distinction.

The detailed checked proof document covers **all of Corollary 3.2 and its proof** from
[arXiv:2609.27634v1](https://arxiv.org/abs/2609.27634v1): the inequality
`|ν(C) − ρ(C)| ≤ 1/4`, both unique extremizers, their coefficient values and support
graphs. The displayed proof follows the published derivative argument. The
comparison column preserves the published wording, including its references.
This is a complete result from the article; it is not yet a proof document for
the entire article. The earlier results it cites remain compiled dependencies.

## Sources and reproduction

- [ArticleBridge.lean](../Papers/Rockel2026ExactBlest/ArticleBridge.lean): precise
  definitions, theorem, definition correspondences, statement equivalence,
  certificate, and transitive axiom audits.
- [ArticlePresentation.lean](../Papers/Rockel2026ExactBlest/ArticlePresentation.lean):
  the original definition vocabulary and inequality bridge.
- [ArticleCalculus.lean](../Papers/Rockel2026ExactBlest/ArticleCalculus.lean):
  the printed derivative signs, strict monotonicity and unique scalar maximum.
- [ArticleProof.lean](../Papers/Rockel2026ExactBlest/ArticleProof.lean): the scoped
  proof tree and its audited `Argument.Valid` certificate.
- [ArticleDocument.lean](../Papers/Rockel2026ExactBlest/ArticleDocument.lean):
  checked definition notation and export through `checked_document%`.
- [ArticleOriginalProof.lean](../Papers/Rockel2026ExactBlest/ArticleOriginalProof.lean):
  additional checks of the exact displayed moments, parameter conventions,
  rectangle factorizations, derivatives and signs in the original proofs.
- [ArticleIndex.lean](../Papers/Rockel2026ExactBlest/ArticleIndex.lean): generated
  registry that extracts real theorem types and audits their transitive axioms.
- [Article map](../examples/paper-bridge/article-map.json): exact label/quotation
  bindings. A missing or ambiguous passage fails the reader build.
- [Generated LaTeX](../examples/paper-bridge/blest-bound.tex) and
  [website data](../examples/paper-bridge/blest-bound.json).

```sh
lake exe cache get
python scripts/lean_mirror.py
python scripts/lean_mirror.py --check
python scripts/lean_mirror_article.py --check
python scripts/test_lean_mirror.py
python scripts/test_paper_source.py
```

The exporter first builds the certificate. `--check` compares both saved outputs
with a fresh export and rejects any stale or manually altered presentation. The
rejection tests include changed formulas, invalid scope, extra axioms, and `sorry`.
They also reject a false intermediate assertion despite a true final conclusion,
changed extremizer values and altered source excerpts. The original source and
line-selected excerpt are pinned by SHA-256 in `examples/paper-bridge/source.json`.

## Website

The site has a LeanMirror entry and a companion at `/lean-mirror/blest-spearman/`.
Its full-article text comes from the exact pinned original LaTeX. The detailed
Corollary 3.2 document is at `/lean-mirror/blest-spearman/corollary-3-2/`;
its theorem and definition formulas come from the generated JSON. Clickable
symbols lead to definitions; correspondence links lead to generated Lean API
declarations. Both publication CI and Lean CI recompile and check freshness.
The reader imports its proof rendering from the pinned LeanMirror dependency;
subject-specific mathematics stays in this repository. A downloadable source
bundle contains the pinned Lake project and all sources needed to check it.

To build a local content preview:

```sh
npm ci --prefix .lake/packages/lean-mirror
npm ci --prefix website
node website/build.mjs --handbook-only
node website/check.mjs --handbook-only
```

## Trust and scope

The mathematical interpretation and equivalence proofs are checked by Lean's
kernel. The statement correspondence is derived from the definition bridges
and applies pointwise at every real bound before being specialized to `1/4`.
That original bridge remains available. The new proof document is checked
independently: `Argument.sound` derives its conclusion from the validity of
every node. `ExistingCorollary` extracts the types of the existing bound,
uniqueness, family-value and graph theorems with `statement_of%`.
`full_correspondence` connects these to the complete proof document by unfolding
definitions, normalizing the parameter and using the survival identities; it
does not appeal to a proof of the corollary. The readable law defining the tent-map copula
also has a checked identity with `paperD unitHalf`.

Recognizing the intended mathematics in the displayed statement and definitions
is a human judgment. The parser, notation, foundational glossary, and rendering
software have not themselves been formally verified. They are documented in
the [LeanMirror repository](https://github.com/Corrram/lean-mirror).

Extend the general language and compiler in LeanMirror. Keep subject-specific
models, vocabulary, definitions, and equivalence proofs in downstream projects
such as this one. Update the pinned dependency only after checking the companions.

## Additional full-article readers

The Chatterjee–Blest companion is at `/lean-mirror/xi-blest/`. It preserves
arXiv:2603.09768v1 in full, including its numerical table and all figure panels.
The two known false printed claims have visible notices and compiled
counterexamples alongside the checked corrections. Its result and calculation
links are compiled counterparts, not a claim that every literal proof step
has been verified.

The corrected lower-clamped square moment now has a scoped, readable proof
document. It evaluates the primitive at `1` and `r` in two separate checked
steps, then subtracts them to obtain the coefficient `-8/15`. Its independently
encoded primitive definition and pointwise statement correspondence are also
checked. This document accompanies an explicit refutation of the printed
`-1/5` coefficient; it does not certify that erroneous original line.

The Blest–Spearman reader embeds four rectangle calculations from Proposition
4.3 as scoped proof documents. The first two check the factorizations and sign
estimates, including the second rectangle's exact equality set. The last two
check the partial derivatives, their signs, comparison with the relevant edge,
vanishing endpoint values, the edge minimum and final nonnegativity. The edge
minimum is proved using monotonicity from the displayed derivatives, as in the
article. Each displayed conclusion has its own interpretation and correspondence
proof. All four documents retain the article's range `1/2 ≤ w < 1`; their
underlying nonnegativity lemmas also cover `w=1`. This does not yet certify the
entire proposition's literal proof or all its equality cases.

All nine other manuscripts have been imported into `examples/articles/` with
versioned arXiv provenance and hashes for every unchanged source file. An import
does not make a manuscript a certified companion. Only directories with an
explicit `article-map.json` are built as article readers.

```sh
python scripts/check_article_sources.py
python scripts/test_article_sources.py
python scripts/lean_mirror_article.py --check
# Recompile one authored map while extending it:
python scripts/lean_mirror_article.py --paper Rockel2026XiBlest
```

Source-to-theorem bindings identify an exact label or a unique literal passage;
there is no fuzzy matching. Each generated registry extracts the actual Lean
theorem type with `checked_native%` and audits its transitive axioms. Full proof
documents additionally use `checked_document%` on a closed validity certificate.
An authored map may name a `proofDocumentNamespace` in the same paper module;
the exporter compiles and extracts that namespace's proof documents alongside
the theorem registry. This lets downstream articles add typed proof passages
without adding subject-specific code to LeanMirror itself.

The Chatterjee–Blomqvist reader at `/lean-mirror/xi-beta/` preserves
arXiv:2606.30033v2, including the original wide title block, section equation
numbers, bibliography and figures. Its date is pinned to the source version;
rendering `\today` never silently substitutes the build date. All thirteen
labeled results have compiled counterparts. The beta and attainable-region
definitions, the exact-region statement and universal cubic inequality have
independent typed encodings and checked correspondence. The region equivalence
uses only interpreted definitions and set extensionality, without invoking the
proved region theorem. The accompanying one-step statement documents reuse
the native theorems; they do not certify the printed proof of Proposition 4.1.
In particular, a full
bridge from the convex-function hypotheses in Lemma 5.2 to the slope-data
encoding remains outstanding. These limits are stated in the reader itself.

An optional `evidenceModule` names a module in the current paper namespace
containing additional definition or statement bridges. It is compiled before
the registry is exported. The subject-specific model stays downstream; the
generic parser and renderer stay in the LeanMirror package.

Article exports sort JSON keys and the axiom/dependency collections so field
ordering cannot invalidate a cross-platform rebuild. Source hashes, theorem
types and ordered proof steps remain exact. A freshness failure reports the
first differing data field rather than just a generic stale-export message.

The Chatterjee–Spearman footrule reader at `/lean-mirror/xi-footrule/` preserves
arXiv:2509.07232v1, including all fourteen definition and result blocks, two
tables, three figures with nine panels, and twenty-seven references. The six
checkerboard panels retain the original two rows of three. Eleven result blocks
have compiled counterparts; the external copula characterization and two KKT
lemmas in the appendix are not covered by these bindings.

The definitions of both coefficients and the Fréchet family have independent
typed encodings and checked correspondence. The complete maximum statement
includes attainment, uniqueness and both endpoints. Its statement certificate
reuses the native theorem; it does not certify the original KKT proof. The
reader also shows two refuted source claims, with the original text intact:
the printed checkerboard matrix is not LTD, and the inverse cubic does not have
a unique unrestricted real root. A separate checked proof document evaluates
the cubic at two distinct roots when `y=-1/2`. The corrected inverse theorem
restricts the root to `[0,2]`. Numerical optimization experiments remain
visible but are not presented as formal proofs.
