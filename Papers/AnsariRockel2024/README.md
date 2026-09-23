# Dependence properties of bivariate copula families

**Jonathan Ansari and Marcus Rockel.** *Dependence Modeling* 12(1), 2024.

- Published article: [10.1515/demo-2024-0002](https://doi.org/10.1515/demo-2024-0002).
- Preprint reference: [arXiv:2310.17307v3](https://arxiv.org/abs/2310.17307v3),
  revised 6 April 2024.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Selected Tables 1-6 results are checked: both Clayton CDF branches, special and limiting cases, and exact signed Clayton CI/CD classification, quadrant dependence, full signed density-TP2 classification and positive-parameter absolute continuity, and both tail coefficients; FGM, Frechet and Mardia association formulas and tails; FGM conditional monotonicity, lower orthant order and exact MTP2 classification of its actual density; Nelsen 7 CDF, endpoints, CD, exact CDF-TP2 and density-TP2 ranges, parameter order and both tail limits. Full-square Joe, positive-parameter Frank, negative Frank in the printed logarithmic form and its independence case at zero, and Nelsen 2, Nelsen 8, Nelsen 12, Nelsen 14, Genest-Ghoudi, Gumbel-Hougaard and Tawn CDF formulas and both tail limits for Gumbel, Marshall-Olkin, Cuadras-Auge and Tawn, the exact FGM Schur order, and the corrected Frechet parameter order are also checked. The exact Frechet and Mardia CI/CD and absolute-continuity/density-TP2 classifications, and an incomparable Mardia pair, are checked as well. Joe, Nelsen 2, and Nelsen 8 now have both exact tail limits; Nelsen 8 also has increasing lower-orthant parameter order. Nelsen 7 now also has its exact conditional CDF, xi=1-theta and rho and tau logarithmic formulas, CI region and Schur parameter order checked. Lemmas 2.6 and 2.8 (both directions on the monotone classes) and Proposition 3.2 are fully checked, as are copula-level concordance and xi consistency and both tail-order implications. Theorem 3.4(i)-(ii) is checked from max-stability, and each directional Schur equivalence and both xi consequences are checked under an explicit CI hypothesis; ordered extreme-value rho, tau and tail limits are also checked; Marshall-Olkin and Cuadras-Auge CI, lower orthant and both-direction Schur parameter orders are checked on the full interval. Cuadras-Auge also has its actual conditional CDF and all three exact Table 6 formulas (rho, xi, tau) checked; Marshall-Olkin has its actual conditional CDF and full two-parameter rho, xi and tau formulas checked. Exact density-TP2 and absolute-continuity classifications are checked for both common-shock families. The arXiv v3 Nelsen 7 xi intermediate integrand is formally refuted throughout the interior parameter range while its final xi formula remains verified. Other family entries, remaining general order correspondences and journal comparison remain pending.
See [SOURCE_COMPARISON.md](SOURCE_COMPARISON.md) for the inspected publisher statements and version-specific printed discrepancies.
See [COVERAGE.md](COVERAGE.md) for exact statements and remaining work.

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
- [Nelsen7Results.lean](Nelsen7Results.lean): full-interval conditional CDF, derivative, xi, exact CI and Schur order.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Association.lean](Association.lean): nine Table 6 coefficient formulas.
- [Nelsen7Rho.lean](Nelsen7Rho.lean) and [Nelsen7Tau.lean](Nelsen7Tau.lean): exact Nelsen 7 logarithmic rho and tau formulas on the full interval.
- [Nelsen7SourceCorrection.lean](Nelsen7SourceCorrection.lean): counterexample to arXiv v3 Appendix A.5.1's printed xi intermediate integral.
- [Dependence.lean](Dependence.lean): selected Table 5 properties.
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
