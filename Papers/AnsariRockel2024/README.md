# Dependence properties of bivariate copula families

**Jonathan Ansari and Marcus Rockel.** *Dependence Modeling* 12(1), 2024.

- Published article: [10.1515/demo-2024-0002](https://doi.org/10.1515/demo-2024-0002).
- Preprint reference: [arXiv:2310.17307v3](https://arxiv.org/abs/2310.17307v3),
  revised 6 April 2024.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: complete for scope.** Every cell that arXiv v3 Tables 1–6 states as a result has a verified row: the CDF/constructor, CI/CD region, density TP2, lower-orthant and Schur parameter orders, tail coefficients, the Table 4 special and limiting cases, and the supplied Table 6 formulas, for all 38 families. The same holds for the general results (Section 2.1 representation, Definition 2.3, Lemmas 2.4, 2.6, 2.7, 2.8, 2.10, Propositions 3.1, 3.2, 3.3, Theorem 3.4). Where the printed source is wrong, the corrected statement is verified and the discrepancy is recorded (e.g. AMH lower tail at θ=1, Raftery CDF, Plackett ρ, Gaussian ξ and tails, Fréchet/Mardia weights, the t-EV ν→∞ limit, the blanket Tawn TP2 exclusion). Cells marked `?` in the source state no result. Numerical-only (`*`) observations are verified where a proof or counterexample was found: all Schur `*` cells, and the Joe-EV/Tawn/t-EV TP2 exclusions at explicit members. The Hüsler–Reiss TP2 claim and the all-parameter EV exclusions are excluded as numerical-only. Numbering follows arXiv v3; publisher-version differences are recorded in SOURCE_COMPARISON.md.
See [SOURCE_COMPARISON.md](SOURCE_COMPARISON.md) for the inspected publisher statements and version-specific printed discrepancies.
See [COVERAGE.md](COVERAGE.md) for exact statements, corrections and the excluded numerical observations.

The pinned `copula` library already contains relevant results and a detailed
[Ansari–Rockel coverage index](https://github.com/Corrram/copula/blob/5bea8507713d490344ab9b0965a2c9cfd841c2e0/docs/ansari-rockel.md).
That index is a starting point for matching definitions, hypotheses, and
individual table entries. It is not a claim of complete formalization of the
article. General library results remain upstream; this folder records
their precise correspondence to the paper and any article-specific proofs.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [ClaytonResults.lean](ClaytonResults.lean): both CDF branches, special/limiting cases, exact signed CI/CD classification, quadrant dependence, CDF-level TP2 classification, and both tail coefficients.
- [ClaytonDensityDerivative.lean](ClaytonDensityDerivative.lean): first and mixed derivatives of the positive Clayton CDF formula and the exact pinned candidate-density integral and `withDensity` measure equality to actual copula mass on positive unit-square rectangles, with quantitative cutoff bounds and convergence to each upper-corner Clayton CDF; extension across the axes proves global measure equality, MTP2 density, and absolute continuity.
- [FamilyExtensions.lean](FamilyExtensions.lean): FGM density and Nelsen 7 dependence, order and tail results.
- [TailsAndOrders.lean](TailsAndOrders.lean): four extreme-value tail pairs, exact FGM Schur order and corrected Frechet order.
- [NamedArchimedeanCDF.lean](NamedArchimedeanCDF.lean): Joe, both signed Frank constructors and the zero case, Nelsen 2, Nelsen 8, Nelsen 12, Nelsen 14 and Genest-Ghoudi Table 1 CDFs on the closed square and their Table 2 endpoints.
- [NamedExtremeValueCDF.lean](NamedExtremeValueCDF.lean): Gumbel-Hougaard and Tawn Table 1 CDFs on the full closed square, including exact Tawn shape and weight-axis reductions.
- [FrechetMardiaDependence.lean](FrechetMardiaDependence.lean): exact CI/CD and density classifications, source corrections and Mardia incomparability.
- [AMHSchur.lean](AMHSchur.lean): exact two-direction Schur parameter order on both same-sign AMH regions.
- [Nelsen7Results.lean](Nelsen7Results.lean): full-interval conditional CDF, derivative, xi, exact CI and Schur order.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Association.lean](Association.lean): nine Table 6 coefficient formulas.
- [Nelsen2Dependence.lean](Nelsen2Dependence.lean): lower-orthant order, non-PQD, non-CI, exact CD range, and CDF/density TP2 exclusions.
- [CDFTotalPositivity.lean](CDFTotalPositivity.lean): full-parameter CDF TP2 for Nelsen 12, Nelsen 14, Gumbel, Tawn, Marshall–Olkin and Cuadras–Augé; density TP2 remains separate.
- [NelsenEndpointDependence.lean](NelsenEndpointDependence.lean): CI, CDF TP2, MTP2 density and non-CD for Nelsen 12 and 14 at the shared Clayton(1) endpoint, plus all-parameter non-CD for both families and PQD for both families.
- [PowerFamilyLimits.lean](PowerFamilyLimits.lean): full-square pointwise comonotonic endpoints for Nelsen 14 and Genest–Ghoudi.
- [GenestGhoudiDependence.lean](GenestGhoudiDependence.lean): exact CI/CD and CDF/density-TP2 classifications, with a positive diagonal zero-CDF witness.
- [GenestGhoudiTails.lean](GenestGhoudiTails.lean): exact lower and upper tail coefficients for every finite admissible parameter.
- [Nelsen14Tails.lean](Nelsen14Tails.lean): exact lower and upper tail coefficients for every finite admissible parameter.
- [Nelsen12Tails.lean](Nelsen12Tails.lean): exact lower and upper tail coefficients for every finite admissible parameter.
- [Nelsen8Dependence.lean](Nelsen8Dependence.lean): non-PQD, non-CI, CDF-TP2 and density-TP2 exclusions, plus the exact CD classification.
- [Nelsen7Rho.lean](Nelsen7Rho.lean) and [Nelsen7Tau.lean](Nelsen7Tau.lean): exact Nelsen 7 logarithmic rho and tau formulas on the full interval.
- [Nelsen7SourceCorrection.lean](Nelsen7SourceCorrection.lean): counterexample to arXiv v3 Appendix A.5.1's printed xi intermediate integral.
- [Dependence.lean](Dependence.lean): selected Table 5 properties.
- [Rearrangement.lean](Rearrangement.lean): Definition 2.3, Lemma 2.4, Lemma 2.7 and Proposition 3.1 (rearranged copulas and the rearrangement Schur order).
- [ArchimedeanOrders.lean](ArchimedeanOrders.lean): Proposition 3.3 (i)–(iii).
- [ClaytonOrders.lean](ClaytonOrders.lean) and [GenestGhoudiOrder.lean](GenestGhoudiOrder.lean): Clayton lower-orthant/Schur orders on the signed range and the Genest–Ghoudi lower-orthant order.
- [SchurUnordered.lean](SchurUnordered.lean) and [Nelsen18Schur.lean](Nelsen18Schur.lean): the unordered Schur cells of Nelsen 2, 8, 15 and 18.
- [FrechetMardiaSchur.lean](FrechetMardiaSchur.lean): Mardia and Fréchet Schur orders.
- [TEV.lean](TEV.lean), [TEVLimits.lean](TEVLimits.lean): the t-EV family in printed Student-t form, its orders, tails, endpoints and ν-limits.
- [TawnTP2Witness.lean](TawnTP2Witness.lean), [JoeExtremeValueTP2.lean](JoeExtremeValueTP2.lean), [TEVTP2Witness.lean](TEVTP2Witness.lean): explicit non-TP2 members.
- [LaplaceBessel.lean](LaplaceBessel.lean), [EllipticalRhoHV.lean](EllipticalRhoHV.lean), [FamilyMappings.lean](FamilyMappings.lean): Laplace Bessel density, Heinen–Valdesogo rho, and remaining mapping rows.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.AnsariRockel2024.Main
lake build
python scripts/check_verification.py
lake env lean Papers/AnsariRockel2024/Axioms.lean
```

The full build checks all paper files and enforces the standard axiom allowlist.
The coverage checker requires matching audits for every verified entry. The
final command also prints those axiom reports. Unlisted article statements
have not been verified by this supplement.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.

The permanent folder identifier is `AnsariRockel2024`.
