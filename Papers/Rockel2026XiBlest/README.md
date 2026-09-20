# The exact region between Chatterjee's and Blest's rank correlations

**Marcus Rockel.** *International Journal of Approximate Reasoning* 197 (2026), article 109744.

- Journal article: [10.1016/j.ijar.2026.109744](https://doi.org/10.1016/j.ijar.2026.109744).
- Source version: [arXiv:2603.09768v1](https://arxiv.org/abs/2603.09768v1), 10 March 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Blest's weighted-CDF convention, monotonicity, affine mixtures, independence normalization, and the xi=0 endpoint are checked. The extremal family and exact region remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The coverage map uses the arXiv version above; correspondence with the journal
version remains to be checked.

The permanent folder identifier is `Rockel2026XiBlest`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Blest.lean](Blest.lean): checked statements and proof steps.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.Rockel2026XiBlest.Main
lake build
python scripts/check_verification.py
lake env lean Papers/Rockel2026XiBlest/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
