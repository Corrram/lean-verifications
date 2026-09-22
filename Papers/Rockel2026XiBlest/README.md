# The exact region between Chatterjee's and Blest's rank correlations

**Marcus Rockel.** *International Journal of Approximate Reasoning* 197 (2026), article 109744.

- Journal article: [10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744).
- Source version: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** The exact xi-Blest region, both explicit coefficient branches, endpoint limits, unique curved-boundary copulas and parameters, convexity, compactness, and the sharp gap 44/105 are checked. The relaxed measurable-kernel optimization problem, normalization-map continuity, and derivative identity including b=1 are also checked. All main and auxiliary results specific to arXiv v1 are checked, including Lemmas 4.1-4.2. A displayed intermediate polynomial is formally refuted and corrected; the final coefficient formulas are verified independently. The author revision's full signed-family concordance ordering, negative-parameter SD, and uniform copula limits at zero and both infinities are also checked. Its positive-parameter MTP2 density claim is also proved. Final journal-version correspondence remains pending.
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
- [HyperbolicCoefficients.lean](HyperbolicCoefficients.lean): both explicit coefficient branches for actual copulas.
- [ExactRegion.lean](ExactRegion.lean): the full explicit region and unique boundary copulas.
- [Derivatives.lean](Derivatives.lean): the derivative identity across the joining point.
- [RelaxedOptimization.lean](RelaxedOptimization.lean): the full measurable-kernel optimization problem.
- [NormalizationContinuity.lean](NormalizationContinuity.lean): continuous normalization and mixture paths.
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
