# The exact Spearman rho-footrule region via optimal transport with applications to finite rankings, mixability, and Chatterjee's rank correlation

**Jonathan Ansari; Marcus Rockel.** Preprint, first submitted 2026.

- Source version: [arXiv:2608.20176v1](https://arxiv.org/abs/2608.20176v1), 20 August 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: scaffold.** No article result is claimed verified yet.
Planned scope: The rho-footrule region and optimal transport proof, with applications tracked separately.
See [COVERAGE.md](COVERAGE.md) for the starting roadmap and remaining work.

The permanent folder identifier is `AnsariRockel2026RhoFootrule`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.AnsariRockel2026RhoFootrule.Main
lake build
lake env lean Papers/AnsariRockel2026RhoFootrule/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports once declarations have been added to `Axioms.lean`. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
