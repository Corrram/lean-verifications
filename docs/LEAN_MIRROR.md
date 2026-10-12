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
