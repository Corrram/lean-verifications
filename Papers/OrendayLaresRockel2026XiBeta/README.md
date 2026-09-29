# The exact region between Chatterjee's ξ and Blomqvist's β

**Jacob Israel Orenday Lares; Marcus Rockel.** Preprint, first submitted 2026.

- Source version: [arXiv:2606.30033v2](https://arxiv.org/abs/2606.30033v2), 29 September 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: complete for stated scope.** Theorems 1.1 and 1.2, Lemmas 2.1, 5.1 and 5.2, Propositions 3.1, 3.2, 4.1, 4.2 and 5.3, Corollary 4.3, Remarks 3.3 and 5.4, the identities (2.2)-(2.4), (5.1)-(5.5), and the quantitative claims of the Introduction and Figure 1 are checked. This includes both exact regions (all copulas and stochastically increasing/decreasing copulas), the explicit interval-exchange copulas D_b and two-branch copulas R_b, all listed tent-copula properties, and density TP2/RR2 under arbitrary nonnegative measurable versions.
See [COVERAGE.md](COVERAGE.md) for the exact declared scope and construction conventions.

The permanent folder identifier is `OrendayLaresRockel2026XiBeta`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [SharpBound.lean](SharpBound.lean): the universal cubic inequality, including singular copulas.
- [LeftBoundary.lean](LeftBoundary.lean): the signed tent copulas, exact coefficients, and uniqueness.
- [LeftProperties.lean](LeftProperties.lean): the conditional kernel, quadrant masses, reflections, symmetry and dependence.
- [Subclasses.lean](Subclasses.lean): symmetric right endpoints, exact subclass regions, and SI/SD inner intervals.
- [RightBoundary.lean](RightBoundary.lean): deterministic copulas with xi=1 at every beta.
- [Mixtures.lean](Mixtures.lean): fixed-beta interpolation.
- [Region.lean](Region.lean): the full exact-region theorem.
- [TentDensity.lean](TentDensity.lean): explicit density, absolute continuity and its three possible values.
- [TentTranspose.lean](TentTranspose.lean): reverse stochastic monotonicity and exchangeability classifications.
- [TentRank.lean](TentRank.lean): rho and tau of the signed tent family.
- [TentTotalPositivity.lean](TentTotalPositivity.lean): TP2/RR2 classifications, independent of density version.
- [StochasticRigidity.lean](StochasticRigidity.lean): maximal xi forces M in SI and W in SD.
- [MedianSection.lean](MedianSection.lean), [MaximalCompletion.lean](MaximalCompletion.lean), [RightSection.lean](RightSection.lean), [GapConvex.lean](GapConvex.lean) (with [GapConvexAux](GapConvexAux.lean), [GapConvexEq](GapConvexEq.lean)), [CompletionXi.lean](CompletionXi.lean), [SIBound.lean](SIBound.lean) (with [SIBoundAux](SIBoundAux.lean), [SIBoundFinal](SIBoundFinal.lean)): Section 5, median sections, maximal completion Q_A, Lemma 5.2, and the SI inequality of Theorem 1.2.
- [RBranchBasic.lean](RBranchBasic.lean), [RBranchOrdinal.lean](RBranchOrdinal.lean), [RBranchLaw.lean](RBranchLaw.lean), [RBranchSingular.lean](RBranchSingular.lean), [RBranchRank.lean](RBranchRank.lean), [RBranchProp53.lean](RBranchProp53.lean): the two-branch copulas R_b (Proposition 5.3).
- [SIRegion.lean](SIRegion.lean), [Remark54.lean](Remark54.lean): the exact SI/SD regions (Theorem 1.2) and Remark 5.4.
- [IntervalExchange.lean](IntervalExchange.lean), [DExchangeShuffle.lean](DExchangeShuffle.lean), [DExchange.lean](DExchange.lean): the explicit interval-exchange copulas D_b (Proposition 4.2).
- [Section2Classes.lean](Section2Classes.lean), [Section4V2.lean](Section4V2.lean): Section 2 identities and classes, Theorem 1.1 and Corollary 4.3 restated, Introduction claims.
- [TentV2Basic.lean](TentV2Basic.lean), [TentV2Prop31.lean](TentV2Prop31.lean), [TentV2Prop32.lean](TentV2Prop32.lean), [TentV2Minimizer.lean](TentV2Minimizer.lean): Propositions 3.1, 3.2 and Remark 3.3 in the notation of v2.
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
