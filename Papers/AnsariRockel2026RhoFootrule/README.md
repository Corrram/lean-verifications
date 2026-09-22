# The exact Spearman rho-footrule region via optimal transport with applications to finite rankings, mixability, and Chatterjee's rank correlation

**Jonathan Ansari; Marcus Rockel.** Preprint, first submitted 2026.

- Source version: [arXiv:2608.20176v1](https://arxiv.org/abs/2608.20176v1), 20 August 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** The exact rho-footrule and mean-variance regions, finite-ranking inequalities, mixability infimum, and xi/correlation-ratio outer bounds are checked. Example 2.8 has its exact folded-uniform law, xi=1/4 and eta=0. Example 2.9 has a uniform quantitative gap. Proposition 2.10 is checked in full: the lower curve, every localized upper branch, compactness and full projection of the seed set, the attained concave upper envelope, and the entire inner enclosure. Remark 2.2 has the exact finite-ranking equality/divisibility criterion and strict correction away from contact means. Optimizer uniqueness, comparison with the earlier rho-footrule curve, finite-ranking asymptotic sharpness, and compactness and upper-maximum attainment for the full xi-eta region remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The permanent folder identifier is `AnsariRockel2026RhoFootrule`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Moments.lean](Moments.lean): checked statements and proof steps.
- [Touchpoints.lean](Touchpoints.lean): the variance equality criterion and all discrete sharp contact points.
- [FoldedExample.lean](FoldedExample.lean): the source folded-uniform law, coefficients, and the horizontal inner segment.
- [QuantitativeRatio.lean](QuantitativeRatio.lean): a uniform gap below the outer bound at xi=1/4.
- [LowerInnerCurve.lean](LowerInnerCurve.lean): the full attained lower inner curve.
- [InnerConvexity.lean](InnerConvexity.lean): tagged constructions and xi-eta convexity.
- [UpperBinaryCurve.lean](UpperBinaryCurve.lean): the first upper inner branch and its conditional distributions.
- [UpperLocalizedCurves.lean](UpperLocalizedCurves.lean): every positive equal-block upper branch.
- [UpperSeedsCompact.lean](UpperSeedsCompact.lean): compactness of the upper seeds and their convex hull.
- [UpperSeedsProjection.lean](UpperSeedsProjection.lean): coverage of every horizontal coordinate.
- [UpperInnerEnvelope.lean](UpperInnerEnvelope.lean): attainment, concavity, and the complete inner enclosure.
- [DiscreteEquality.lean](DiscreteEquality.lean): the exact finite-size equality criterion and strict correction.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.AnsariRockel2026RhoFootrule.Main
lake build
python scripts/check_verification.py
lake env lean Papers/AnsariRockel2026RhoFootrule/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.

## Exact-region package integration

- [ExactRegion.lean](ExactRegion.lean).
- [BoundaryFormula.lean](BoundaryFormula.lean).
- [Dispersion.lean](Dispersion.lean).

## Verified applications

- [MeanVariance.lean](MeanVariance.lean) and [VarianceMaximum.lean](VarianceMaximum.lean): exact mean–variance region and its universal maximum.
- [FiniteRankings.lean](FiniteRankings.lean): normalized and unnormalized ranking inequalities.
- [Mixability.lean](Mixability.lean): the attained centered-sum optimization problem.
- [CorrelationRatio.lean](CorrelationRatio.lean): conditional-copy construction, xi–eta outer bounds and strictness.
