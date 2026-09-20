# The exact region determined by Spearman's rho and Gini's gamma

**Jonathan Ansari; Marcus Rockel; Stefanie Steinmaßl.** Preprint, first submitted 2026.

- Source version: [arXiv:2609.19890v1](https://arxiv.org/abs/2609.19890v1), 17 September 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** The full sign-magnitude representation, arbitrary-law converse, sign-bound attainment and equality of the attained support and transport maxima are checked. Weak duality, contact certificates and the half-shift optimizer for s>=1 are checked. The remaining optimizer branches, glued potential, general strong duality and exact boundary remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The permanent folder identifier is `AnsariRockelSteinmassl2026RhoGamma`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [Moments.lean](Moments.lean): checked statements and proof steps.
- [SignMagnitude.lean](SignMagnitude.lean): uniform magnitudes and both sign-moment identities.
- [SignConverse.lean](SignConverse.lean): recovery of arbitrary joint magnitude/sign laws.
- [SignAttainment.lean](SignAttainment.lean): sign-bound attainment and equality of the attained maxima.
- [Transport.lean](Transport.lean): supporting inequality, weak duality and contact-set optimality.
- [HalfShift.lean](HalfShift.lean): the half-shift optimizer and dual certificate for s>=1.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.AnsariRockelSteinmassl2026RhoGamma.Main
lake build
python scripts/check_verification.py
lake env lean Papers/AnsariRockelSteinmassl2026RhoGamma/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.
