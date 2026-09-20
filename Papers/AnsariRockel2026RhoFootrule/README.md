# The exact Spearman rho-footrule region via optimal transport with applications to finite rankings, mixability, and Chatterjee's rank correlation

**Jonathan Ansari; Marcus Rockel.** Preprint, first submitted 2026.

- Source version: [arXiv:2608.20176v1](https://arxiv.org/abs/2608.20176v1), 20 August 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Moment identities, the classical quadratic bound and its constant-displacement equality criterion, all discrete upper-bound contact points, and fixed-footrule interpolation are checked. The sharp correction between contact points, uniqueness, full boundary and applications remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The permanent folder identifier is `AnsariRockel2026RhoFootrule`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Moments.lean](Moments.lean): checked statements and proof steps.
- [Touchpoints.lean](Touchpoints.lean): the variance equality criterion and all discrete sharp contact points.
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
