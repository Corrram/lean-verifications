# Rank weighting and asymmetry in Blest's rank correlation: two exact regions

Marcus Rockel (2026). [Preprint, arXiv:2609.27634v1](https://arxiv.org/abs/2609.27634v1).

**Verification: complete for stated scope.** All labeled mathematical results of arXiv:2609.27634v1: both exact regions, unique boundary copulas, sharp discrepancies, the transpose region, rearrangement and dual-certificate lemmas, explicit extremal families and conditional laws. Quantitative claims and figure values are included; historical discussion and literal proof prose are excluded.

[Coverage and mathematical audit](COVERAGE.md) maps the manuscript to fully
qualified declarations. The 23 imported proof modules contain 592 theorem
statements, each with a standard-axiom assertion. [Axioms.lean](Axioms.lean)
also prints and checks every theorem advertised in the coverage table.
The retained beta/Blest modules prove earlier results and supply infrastructure;
the beta region is not a claim of this preprint.

## Reproduction

Run from the repository root, using the pinned Lean toolchain and manifest:

```sh
lake exe cache get
lake build
python scripts/check_verification.py
lake env lean Papers/Rockel2026ExactBlest/Axioms.lean
```

The entry point is `Papers.Rockel2026ExactBlest.Main`. The proof sources were imported from
`copulas_in_systemic_risk/xi-blest/lean` (23 September 2026 manuscript revision).
Only module paths and the namespace were changed. Shared CDF-based Blest
infrastructure is in `Verification/Blest`; its original public namespace is
preserved for compatibility with the xi–Blest supplement. This project has
no dependency on a sibling manuscript checkout or nested Lake project.

The manuscript parametrization is exposed by `paperD`, `paperA`, and `paperB`.
The coverage map records reflected internal parameters and alternative proof
routes, including endpoint conventions and conditional-law interpretation.
Historical prose and bibliographic claims are outside the formal scope.

The independent symbolic checks are also included. With SymPy 1.14.0 installed,
run `python Papers/Rockel2026ExactBlest/verify_symbolic.py` from the root.
They check 82 exact identities and supplement the Lean proofs; they do not
establish the exact-region or uniqueness theorems on their own.
See [the validation record](VALIDATION.md) for the checks performed here.

For citation use [references.bib](references.bib) for the article, and a full
repository commit permalink for the exact supplement snapshot, as described
in [the publication guide](../../docs/PUBLISHING.md).
