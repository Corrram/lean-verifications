# The exact region and an inequality between Chatterjee's and Spearman's rank correlations

**Jonathan Ansari; Marcus Rockel.** *Journal of Multivariate Analysis* 214 (2026), article 105630.

- Journal article: [10.1016/j.jmva.2026.105630](https://doi.org/10.1016/j.jmva.2026.105630).
- Source version: [arXiv:2506.15897v3](https://arxiv.org/abs/2506.15897v3), 19 May 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: complete for stated scope.** Theorems 1-3, Corollary 1, Propositions 1-5, and Example 1 are checked for the corrected arXiv v3 copula, including all boundary and equality cases. The family has an explicit density, convex topological support, MTP2, asymmetry, all three rank formulas, ordering and uniform limits. Journal equation (19) lacks a necessary boundary term; its literal formula is disproved in Lean. Lemma 8 uses equality almost everywhere. Alternative proofs replace unused optimization and rearrangement intermediates.
See [COVERAGE.md](COVERAGE.md) for exact statements and source corrections.

The coverage map uses corrected arXiv v3. The journal equation (19) discrepancy is documented and has a formal counterexample.

The permanent folder identifier is `AnsariRockel2026XiRho`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [SelectedResults.lean](SelectedResults.lean): checked statements and proof steps.
- [RightBoundary.lean](RightBoundary.lean): the complete xi=1 boundary, with radially symmetric witnesses.
- [StochasticBounds.lean](StochasticBounds.lean): general SI/SD rho bounds and the weighted derivative formula.
- [StochasticEquality.lean](StochasticEquality.lean): all SI/SD equality cases and Lemma 8 modulo null sets.
- [RegionGeometry.lean](RegionGeometry.lean): convexity and attainment at fixed coefficient.
- [DiagonalBandUnit.lean](DiagonalBandUnit.lean): the actual unit-slope diagonal-band copula and its conditional CDF.
- [SharpGap.lean](SharpGap.lean): Corollary 1, with exact coefficients, the universal bound, and unique attainment.
- [SharpSlice.lean](SharpSlice.lean): both gap signs and the exact xi=3/10 slice.
- [BandOptimization.lean](BandOptimization.lean): all nonnegative normalized slopes and their unique global optimality.
- [SourceBand.lean](SourceBand.lean): the source piecewise intercept, actual copula, and derivative correspondence.
- [BandCoefficients.lean](BandCoefficients.lean): exact xi and rho on both parameter ranges.
- [BoundaryInverse.lean](BoundaryInverse.lean): the displayed trigonometric and radical inverse formulas.
- [ExactRegion.lean](ExactRegion.lean): the full explicit region and unique interior boundary copulas.
- [BandSymmetry.lean](BandSymmetry.lean): radial symmetry and negative-parameter correspondence.
- [BandOrder.lean](BandOrder.lean): pointwise parameter ordering.
- [BandLimits.lean](BandLimits.lean): uniform limiting cases with quantitative error bounds.
- [PlodExample.lean](PlodExample.lean): the four-strip PLOD counterexample.
- [BandCDF.lean](BandCDF.lean): the corrected piecewise CDF and journal counterexample.
- [BandKendall.lean](BandKendall.lean): Kendall tau for all parameters, derived from the actual sampling law.
- [BandDensity.lean](BandDensity.lean): absolute continuity and MTP2.
- [BandDensityOpen.lean](BandDensityOpen.lean): the exact open-band density convention.
- [BandSupport.lean](BandSupport.lean): exact convex topological support.
- [BandAsymmetry.lean](BandAsymmetry.lean): non-exchangeability for both signs.
- [NegativeBandDensity.lean](NegativeBandDensity.lean): the reflected density and absolute continuity.
- [SignedBand.lean](SignedBand.lean): cross-zero ordering and negative conditional distributions.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.AnsariRockel2026XiRho.Main
lake build
python scripts/check_verification.py
lake env lean Papers/AnsariRockel2026XiRho/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
