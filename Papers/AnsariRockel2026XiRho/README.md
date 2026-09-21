# The exact region and an inequality between Chatterjee's and Spearman's rank correlations

**Jonathan Ansari; Marcus Rockel.** *Journal of Multivariate Analysis* 214 (2026), article 105630.

- Journal article: [10.1016/j.jmva.2026.105630](https://doi.org/10.1016/j.jmva.2026.105630).
- Source version: [arXiv:2506.15897v3](https://arxiv.org/abs/2506.15897v3), 19 May 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** The derivative conventions, endpoints, entire xi=1 boundary, convexity of the full region, and attainment from any existing point up to xi=1 at fixed rho are checked. The full SI/SD Theorem 2 with all equality cases and Lemma 8 modulo null sets are verified. The curved diagonal-band boundary, full explicit region, and sharp global gap remain pending.
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
