# On the exact region between Chatterjee's rank correlation and Spearman's footrule

**Marcus Rockel.** *Journal of Computational and Applied Mathematics* 485 (2026), article 117466.

- Journal article: [10.1016/j.cam.2026.117466](https://doi.org/10.1016/j.cam.2026.117466).
- Source version: [arXiv:2509.07232v1](https://arxiv.org/abs/2509.07232v1), 8 September 2025.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Theorems 2.1, 2.4, and 3.4, Proposition 2.2, and Corollary 2.5 are checked, including the full SI region and bottom boundary. Theorem 3.2 is checked in exact integral form with the piecewise optimizer and Jensen equality criterion. Closed-form relaxed coefficients, global region geometry and parameter inversion, Remark 2.3 refinements, remaining constructions, and journal-version comparison are pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The roadmap uses the arXiv version above; correspondence with the journal
version remains to be checked.

The permanent folder identifier is `Rockel2026XiFootrule`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [LowerEndpoint.lean](LowerEndpoint.lean): the unique checkerboard minimum and full bottom boundary.
- [SIRegion.lean](SIRegion.lean): the exact SI region, explicit boundary witnesses, and the Kendall bound.
- [SIEquality.lean](SIEquality.lean): Proposition 2.2, with measurable cut functions and both conditional-CDF and derivative formulations.
- [LowerBound.lean](LowerBound.lean): Theorem 3.2 in exact integral form, the piecewise optimizer, and the Jensen equality criterion.
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
