# The exact region and an inequality between Chatterjee's and Spearman's rank correlations

**Jonathan Ansari; Marcus Rockel.** *Journal of Multivariate Analysis* 214 (2026), article 105630.

- Journal article: [10.1016/j.jmva.2026.105630](https://doi.org/10.1016/j.jmva.2026.105630).
- Source version: [arXiv:2506.15897v3](https://arxiv.org/abs/2506.15897v3), 19 May 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** The full SI/SD Theorem 2 and Corollary 1's sharp global gap 2/5 are verified, including every equality case. The unit-slope diagonal-band copula is constructed with exact xi=3/10 and rho=7/10; the entire xi=3/10 slice is checked. Normalized clamped copulas are constructed for every nonnegative slope, with SI and unique global support optimality. The xi=1 boundary and full-region convexity remain checked. The general explicit intercept and coefficient formulas, inverse boundary parameter, full explicit region, further family properties, and journal-version comparison remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The coverage map uses the arXiv version above; correspondence with the journal
version remains to be checked.

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
