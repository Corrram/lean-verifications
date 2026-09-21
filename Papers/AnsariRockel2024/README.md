# Dependence properties of bivariate copula families

**Jonathan Ansari and Marcus Rockel.** *Dependence Modeling* 12(1), 2024.

- Published article: [10.1515/demo-2024-0002](https://doi.org/10.1515/demo-2024-0002).
- Preprint reference: [arXiv:2310.17307v3](https://arxiv.org/abs/2310.17307v3),
  revised 6 April 2024.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Selected Tables 1-6 results are checked: FGM, Frechet and Mardia association formulas and tails; FGM conditional monotonicity, lower orthant order and its actual density with TP2 classification; Nelsen 7 CDF, endpoints, CD, parameter order and both tail limits. Both tail limits for Gumbel, Marshall-Olkin, Cuadras-Auge and Tawn, the exact FGM Schur order, and the corrected Frechet parameter order are also checked. Other family entries, general order correspondences and journal comparison remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements and remaining work.

The pinned `copula` library already contains relevant results and a detailed
[Ansari–Rockel coverage index](https://github.com/Corrram/copula/blob/5d7fba65b37e50b86194e0a9938f42513e4403be/docs/ansari-rockel.md).
That index is a starting point for matching definitions, hypotheses, and
individual table entries. It is not a claim of complete formalization of the
article. General library results remain upstream; this folder records
their precise correspondence to the paper and any article-specific proofs.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [FamilyExtensions.lean](FamilyExtensions.lean): FGM density and Nelsen 7 dependence, order and tail results.
- [TailsAndOrders.lean](TailsAndOrders.lean): four extreme-value tail pairs, exact FGM Schur order and corrected Frechet order.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Association.lean](Association.lean): nine Table 6 coefficient formulas.
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
