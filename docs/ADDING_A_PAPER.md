# Adding a paper

1. Choose a permanent Lean identifier, such as `Author2026ShortTitle`. Use an
   uppercase initial letter and ASCII letters or digits only. Do not rename
   published folders when bibliographic details change.
2. Run `python scripts/new_paper.py Author2026ShortTitle` from the repository
   root. The helper refuses to overwrite an existing folder. Python 3.11+ is
   needed only for this helper, not for building the Lean supplement.
3. Fill in `paper.toml`: title, full author list, journal status, DOI, and the
   exact arXiv version used. Keep unknown fields empty. Pick the source version
   whose result numbering the coverage map uses; journal and preprint numbers
   may differ. Supply the article citation in `references.bib`.
4. Complete the folder's README with the intended scope and source links. List
   the article in the root README and `Papers/README.md`.
5. Add article-specific definitions in `Definitions.lean`, and create focused
   files such as `Section3.lean` or `RankBounds.lean` as needed. Use
   `namespace Papers.Author2026ShortTitle`; import public result modules in
   `Main.lean`. Lake automatically builds all files under `Papers/`.
6. Map each source result to a fully qualified Lean declaration in
   `COVERAGE.md`. Record source version, parameter range, extra assumptions,
   equivalences of definitions, and anything excluded. Add `#print axioms`
   commands to `Axioms.lean` for the claimed final results. Import
   `Verification.AxiomAudit` and add `#assert_standard_axioms` for each of
   those same fully qualified theorem names. Keep one command per line.
7. Run `lake build`, review the axiom reports, and follow the
   [publication guide](PUBLISHING.md) when the selected scope is ready.

To inspect the axiom reports explicitly, run:

```sh
lake env lean Papers/Author2026ShortTitle/Axioms.lean
python scripts/check_verification.py
```

The Lean assertions fail the build unless each declaration is a theorem whose
transitive axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
The coverage checker requires every `verified` row to contain fully qualified
theorem names in backticks and checks that the assertions and printed reports
match those names exactly. CI runs both checks before publication. These checks
enforce the proof audit; authors must still review the mathematical correspondence
between the formal statement and the cited source.

## Status conventions

The website discovers completed paper metadata automatically. Its paper page
uses `paper.toml`, `COVERAGE.md`, and `references.bib`; new Lean modules enter
the doc-gen4 import index on the next build. See [WEBSITE.md](WEBSITE.md) for
preview and publication commands.

`paper.toml` records the supplement's overall `verification_status`:

| Status | Meaning |
| --- | --- |
| `scaffold` | Metadata and source layout only; no claim of article verification |
| `in-progress` | Some identified results have checked proofs; gaps remain |
| `complete-for-scope` | Every result in the explicitly declared scope is mapped and checked |

Use `pending`, `verified`, or `excluded` for individual coverage rows. A result
proved only with additional hypotheses should be described as that restricted
result, with the gap to the original statement still recorded. Numerical plots
or conjectures are not Lean proofs. A theorem available upstream becomes a
verified coverage row only after its statement and assumptions are matched to
the source and its use is checked in this supplement.

## Shared environment

All papers share the root `lean-toolchain` and `lake-manifest.json`. Do not put
another Lake project inside a paper folder. Paper modules can import `Copula`,
mathlib, and shared `Verification` helpers; avoid importing another paper's
private implementation. When upgrading the shared environment, rebuild all
papers. The commit cited in a publication remains its reproducible snapshot.
