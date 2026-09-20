# The exact region between Chatterjee's ξ and Blomqvist's β

**Jacob Israel Orenday Lares; Marcus Rockel.** Preprint, first submitted 2026.

- Source version: [arXiv:2606.30033v1](https://arxiv.org/abs/2606.30033v1), 29 June 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Theorem 1 is checked: the exact xi-beta region, both attaining boundaries, and uniqueness of the lower boundary. Density and further structural properties of the tent family, classical rank formulas, and Section 6 subclasses remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The permanent folder identifier is `OrendayLaresRockel2026XiBeta`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [SharpBound.lean](SharpBound.lean): the universal cubic inequality, including singular copulas.
- [LeftBoundary.lean](LeftBoundary.lean): the signed tent copulas, exact coefficients, and uniqueness.
- [RightBoundary.lean](RightBoundary.lean): deterministic copulas with xi=1 at every beta.
- [Mixtures.lean](Mixtures.lean): fixed-beta interpolation.
- [Region.lean](Region.lean): the full exact-region theorem.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.OrendayLaresRockel2026XiBeta.Main
lake build
python scripts/check_verification.py
lake env lean Papers/OrendayLaresRockel2026XiBeta/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
