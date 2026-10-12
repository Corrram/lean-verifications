# LeanMirror mathematical companions

[LeanMirror](https://github.com/Corrram/lean-mirror) supplies a reusable language
for precise mathematical statements, their interpretation in Lean, and their
readable presentation. This repository consumes the exact Git commit pinned in
`lakefile.toml` and `lake-manifest.json`.

The first companion is the universal Blest–Spearman inequality
`|ν(C) − ρ(C)| ≤ 1/4`, from arXiv:2609.27634v1, Corollary 3.2. It includes the
copula, CDF, and coefficient definitions and checked correspondence proofs.
Sharpness and equality cases are outside this companion's certificate.

## Sources and reproduction

- [ArticleBridge.lean](../Papers/Rockel2026ExactBlest/ArticleBridge.lean): precise
  definitions, theorem, definition correspondences, statement equivalence,
  certificate, and transitive axiom audits.
- [ArticlePresentation.lean](../Papers/Rockel2026ExactBlest/ArticlePresentation.lean):
  vocabulary, definition closure, and export of the checked expressions.
- [Generated LaTeX](../examples/paper-bridge/blest-bound.tex) and
  [website data](../examples/paper-bridge/blest-bound.json).

```sh
lake exe cache get
python scripts/lean_mirror.py
python scripts/lean_mirror.py --check
python scripts/test_lean_mirror.py
```

The exporter first builds the certificate. `--check` compares both saved outputs
with a fresh export and rejects any stale or manually altered presentation. The
rejection tests include changed formulas, invalid scope, extra axioms, and `sorry`.

## Website

The site has a LeanMirror entry and a companion at `/lean-mirror/blest-spearman/`.
Its theorem and definition formulas come from the generated JSON. Clickable
symbols lead to definitions; correspondence links lead to generated Lean API
declarations. Both publication CI and Lean CI recompile and check freshness.

## Trust and scope

The mathematical interpretation and equivalence proofs are checked by Lean's
kernel. The statement correspondence is derived from the definition bridges
and applies pointwise at every real bound before being specialized to `1/4`.
The existing inequality proof then supplies a proof of the companion.

Recognizing the intended mathematics in the displayed statement and definitions
is a human judgment. The parser, notation, foundational glossary, and rendering
software have not themselves been formally verified. They are documented in
the [LeanMirror repository](https://github.com/Corrram/lean-mirror).

Extend the general language and compiler in LeanMirror. Keep subject-specific
models, vocabulary, definitions, and equivalence proofs in downstream projects
such as this one. Update the pinned dependency only after checking the companions.
