# __PAPER_ID__

Replace this heading with the article title and add its authors, venue, DOI,
and versioned arXiv link. Record the same metadata in [paper.toml](paper.toml)
and the article citation in [references.bib](references.bib).

**Verification status: scaffold.** No article results have been formalized in
this folder yet. Define the intended scope and keep
[COVERAGE.md](COVERAGE.md) current as proofs are added.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.__PAPER_ID__.Main
lake build
lake env lean Papers/__PAPER_ID__/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports once declarations have been added to `Axioms.lean`. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
