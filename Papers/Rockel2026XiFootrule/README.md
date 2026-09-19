# On the exact region between Chatterjee's rank correlation and Spearman's footrule

**Marcus Rockel.** *Journal of Computational and Applied Mathematics* 485 (2026), article 117466.

- Journal article: [10.1016/j.cam.2026.117466](https://doi.org/10.1016/j.cam.2026.117466).
- Source version: [arXiv:2509.07232v1](https://arxiv.org/abs/2509.07232v1), 8 September 2025.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: scaffold.** No article result is claimed verified yet.
Planned scope: Upper boundary and equality cases, the stochastically increasing subregion, and lower bounds for the xi-footrule region.
See [COVERAGE.md](COVERAGE.md) for the starting roadmap and remaining work.

The roadmap uses the arXiv version above; correspondence with the journal
version remains to be checked.

The permanent folder identifier is `Rockel2026XiFootrule`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.Rockel2026XiFootrule.Main
lake build
lake env lean Papers/Rockel2026XiFootrule/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports once declarations have been added to `Axioms.lean`. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
