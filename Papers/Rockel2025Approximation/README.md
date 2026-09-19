# Measures of association for approximating copulas

**Marcus Rockel.** Preprint, first submitted 2025.

- Source version: [arXiv:2505.08045v2](https://arxiv.org/abs/2505.08045v2), 22 May 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: scaffold.** No article result is claimed verified yet.
Planned scope: Association formulas for approximating copulas and checkerboard approximation results under the source hypotheses.
See [COVERAGE.md](COVERAGE.md) for the starting roadmap and remaining work.

The permanent folder identifier is `Rockel2025Approximation`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.Rockel2025Approximation.Main
lake build
lake env lean Papers/Rockel2025Approximation/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports once declarations have been added to `Axioms.lean`. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
