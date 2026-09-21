# The exact region determined by Kendall's tau, Spearman's footrule and Blomqvist's beta

**Jacob Israel Orenday Lares; Marcus Rockel.** Preprint, first submitted 2026.

- Source version: [arXiv:2607.12841v1](https://arxiv.org/abs/2607.12841v1), 14 July 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: complete for stated scope.** Theorem 1.1, Proposition 2.1, Lemma 3.1, Propositions 3.2-3.3, Corollaries 4.1-4.2, the boundary-edge and fibre-symmetry claims, and Section 5's area, unique maximum and volume are checked. This includes arbitrary signed shuffles with zero-width strips, both joint faces, and actual copula attainment of every admissible triple.
See [COVERAGE.md](COVERAGE.md) for exact statements and conventions.

The permanent folder identifier is `OrendayLaresRockel2026TauFootruleBeta`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Mixtures.lean](Mixtures.lean): checked statements and proof steps.
- [CenteredOrdinal.lean](CenteredOrdinal.lean): the centered copula construction and equation (9).
- [FootruleBeta.lean](FootruleBeta.lean): the sharp upper footrule-beta bound and its attaining family.
- [FootruleBetaLower.lean](FootruleBetaLower.lean): the lower footrule-beta bound, its seed and exact pairwise region.
- [PairwiseRegions.lean](PairwiseRegions.lean): tau-footrule and tau-beta inequalities and exact regions.
- [LowerJointFace.lean](LowerJointFace.lean): all joint outer bounds and simultaneous attainment of the entire lower tau face.
- [ShuffleFormula.lean](ShuffleFormula.lean): the general signed shuffle tau identity, including degenerate strips.
- [UpperSeed.lean](UpperSeed.lean): the exact six-strip upper seed and all three coefficients.
- [JointRegion.lean](JointRegion.lean): the upper face and both directions of Theorem 1.1.
- [JointGeometry.lean](JointGeometry.lean): compactness, convexity, rectangular sections and fibre symmetry.
- [JointVolume.lean](JointVolume.lean): section areas, their unique maximum and the region volume 31/40.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and precise scope.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.OrendayLaresRockel2026TauFootruleBeta.Main
lake build
python scripts/check_verification.py
lake env lean Papers/OrendayLaresRockel2026TauFootruleBeta/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
