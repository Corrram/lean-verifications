# Dependence properties of bivariate copula families

**Jonathan Ansari and Marcus Rockel.** *Dependence Modeling* 12(1), 2024.

- Published article: [10.1515/demo-2024-0002](https://doi.org/10.1515/demo-2024-0002).
- Preprint reference: [arXiv:2310.17307v3](https://arxiv.org/abs/2310.17307v3),
  revised 6 April 2024.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: scaffold.** This is the home for the article's Lean
supplement. No article result has yet been mapped to a checked declaration in
this folder. The initial roadmap uses arXiv v3; journal numbering and any
differences between versions still need comparison. See [COVERAGE.md](COVERAGE.md).

The pinned `copula` library already contains relevant results and a detailed
[Ansari–Rockel coverage index](https://github.com/Corrram/copula/blob/f3594c079d205f717fc17a6563e7200251d37f30/docs/ansari-rockel.md).
That index is a starting point for matching definitions, hypotheses, and
individual table entries. It is not a claim of complete formalization of the
article. General library results remain upstream; this folder will record
their precise correspondence to the paper and any article-specific proofs.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.AnsariRockel2024.Main
lake build
lake env lean Papers/AnsariRockel2024/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports once declarations have been added to `Axioms.lean`. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.

The permanent folder identifier is `AnsariRockel2024`.
