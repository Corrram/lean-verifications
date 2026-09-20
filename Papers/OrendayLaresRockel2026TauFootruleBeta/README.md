# The exact region determined by Kendall's tau, Spearman's footrule and Blomqvist's beta

**Jacob Israel Orenday Lares; Marcus Rockel.** Preprint, first submitted 2026.

- Source version: [arXiv:2607.12841v1](https://arxiv.org/abs/2607.12841v1), 14 July 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Biaffinity, fixed-footrule/fixed-beta interpolation, and all centered ordinal-sum identities in equation (9) are checked. Pairwise bounds, simultaneous boundary shuffles, and the full joint region remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The permanent folder identifier is `OrendayLaresRockel2026TauFootruleBeta`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Mixtures.lean](Mixtures.lean): checked statements and proof steps.
- [CenteredOrdinal.lean](CenteredOrdinal.lean): the centered copula construction and equation (9).
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.OrendayLaresRockel2026TauFootruleBeta.Main
lake build
python scripts/check_verification.py
lake env lean Papers/OrendayLaresRockel2026TauFootruleBeta/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
