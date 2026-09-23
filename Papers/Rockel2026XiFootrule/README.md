# On the exact region between Chatterjee's rank correlation and Spearman's footrule

**Marcus Rockel.** *Journal of Computational and Applied Mathematics* 485 (2026), article 117466.

- Journal article: [10.1016/j.cam.2026.117466](https://doi.org/10.1016/j.cam.2026.117466).
- Source version: [arXiv:2509.07232v1](https://arxiv.org/abs/2509.07232v1), 8 September 2025.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Theorems 2.1, 2.4, 3.2, and 3.4, Propositions 2.2, 3.1, and 3.5, and Corollary 2.5 are checked. Theorem 3.3's convexity, entire xi=1 boundary, fixed-footrule interpolation, and exact nonnegative-footrule region are verified. Its inverse lower estimate is checked for footrule in [-1/2,0], with parameter uniqueness on [0,2]. Remark 2.3's asymmetric SI equality example is constructed and checked, including its derivative, xi=footrule=1/2, and asymmetry. The two-parameter density construction is checked on the full closed parameter square, including its independence and checkerboard endpoints. The full region is now proved closed and compact, and every boundary slice attains its extremum. The printed LTD example is proved not LTD; a corrected LTD example with exact ranks is supplied. The exact lower-semilinear region is proved independently of stochastic increase. Finite nested ordinal sums of independence and comonotonic blocks are now proved SI and symmetric with xi=footrule; SI is also preserved by binary ordinal sums, and the interior equality converse is checked for SI components. Adjacent countable sums of independence blocks are now proved symmetric with binary splits at every partition endpoint, an exact Pi first component, a recursive tail decomposition, stochastic increase, and xi=footrule equality. For arbitrary adjacent countable blocks, SI and exchangeability hold exactly when they hold in each block; in the SI class xi=footrule also holds exactly when it holds in each block. In particular, every adjacent countable Pi/M sum is symmetric, SI and has xi=footrule. The full arbitrary-interval converse classification and final publisher-version comparison remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The roadmap uses the arXiv version above; correspondence with the journal
version remains to be checked.

The permanent folder identifier is `Rockel2026XiFootrule`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [LowerEndpoint.lean](LowerEndpoint.lean): the unique checkerboard minimum and full bottom boundary.
- [SIRegion.lean](SIRegion.lean): the exact SI region, explicit boundary witnesses, and the Kendall bound.
- [SIEquality.lean](SIEquality.lean): Proposition 2.2, with measurable cut functions and both conditional-CDF and derivative formulations.
- [SymmetricOrdinalEquality.lean](SymmetricOrdinalEquality.lean): finite nested ordinal-sum symmetry and rank equality, plus the SI-component binary converse.
- [SymmetricOrdinalSI.lean](SymmetricOrdinalSI.lean): SI preservation by ordinal sums and finite symmetric SI equality witnesses.
- [CountableOrdinalPartial.lean](CountableOrdinalPartial.lean): symmetry, endpoint decompositions, and the exact first component for adjacent countable Pi sums.
- [CountableOrdinalTail.lean](CountableOrdinalTail.lean): recursive tail decomposition, stochastic increase and exact xi=footrule equality for adjacent countable Pi sums.
- [CountableOrdinalGeneral.lean](CountableOrdinalGeneral.lean): arbitrary-block countable decomposition and rank equality, with exchangeability for Pi/M blocks.
- [CountableOrdinalMixedSI.lean](CountableOrdinalMixedSI.lean): section-local proof that adjacent countable Pi/M sums are SI.
- [CountableOrdinalSI.lean](CountableOrdinalSI.lean): exact componentwise SI, exchangeability, and SI rank-equality criteria for arbitrary adjacent countable component sequences.
- [LowerBound.lean](LowerBound.lean): Theorem 3.2 in exact integral form, the piecewise optimizer, and the Jensen equality criterion.
- [ClosedCoefficients.lean](ClosedCoefficients.lean): Proposition 3.1, the admissible cubic inverse, and the explicit lower estimate.
- [RegionGeometry.lean](RegionGeometry.lean): convexity and attainment at fixed coefficient.
- [AsymmetricEquality.lean](AsymmetricEquality.lean): the actual asymmetric SI equality copula in Remark 2.3.
- [TwoParameter.lean](TwoParameter.lean): Proposition 3.5, the exact density, finite-mu path, and independence/checkerboard endpoints.
- [ClosedRegion.lean](ClosedRegion.lean): closedness, compactness, and attainment of slice extrema.
- [LTDExample.lean](LTDExample.lean): formal disproof of the printed LTD claim and an exact corrected counterexample.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [UpperBoundary.lean](UpperBoundary.lean): upper boundary and maximal gap proofs.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.Rockel2026XiFootrule.Main
lake build
python scripts/check_verification.py
lake env lean Papers/Rockel2026XiFootrule/Axioms.lean
```

The full build checks all paper files and enforces the standard axiom allowlist.
The coverage checker requires matching audits for every verified entry. The
final command also prints those axiom reports. The entire article is not yet
formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.

Additional checked results: [FrechetMinimum.lean](FrechetMinimum.lean) gives exact xi-plus-footrule minimum and unique minimizer over the full Frechet family, with the Table 2 parameter convention clarified.
