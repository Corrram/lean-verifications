# The exact region between Chatterjee's and Blest's rank correlations

**Marcus Rockel.** *International Journal of Approximate Reasoning* 197 (2026), article 109744.

- Journal article: [10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744).
- Source version: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Blest normalization, range, mixtures, reflection symmetry, the xi=0 endpoint, entire xi=1 boundary, convexity of the full region, and attainment from any existing point up to xi=1 at fixed Blest value are checked. Closedness, compactness, and attainment of both Blest extrema at each xi and the least xi at each Blest value are now checked. The curved extremal family, coefficient formulas, full explicit region, maximal gap, and journal comparison remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The coverage map uses the arXiv version above; correspondence with the journal
version remains to be checked.

The permanent folder identifier is `Rockel2026XiBlest`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Blest.lean](Blest.lean): the weighted CDF functional and mixture identities.
- [Normalization.lean](Normalization.lean): M/W normalization, range and joint reflection symmetry.
- [RightBoundary.lean](RightBoundary.lean): the Blest-rho identity under radial symmetry and complete xi=1 boundary.
- [RegionGeometry.lean](RegionGeometry.lean): convexity and attainment at fixed coefficient.
- [ClosedRegion.lean](ClosedRegion.lean): closedness, compactness, and attainment of slice extrema.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.Rockel2026XiBlest.Main
lake build
python scripts/check_verification.py
lake env lean Papers/Rockel2026XiBlest/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
