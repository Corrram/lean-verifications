## Start with the coverage map

Each article folder contains a `paper.toml` record, bibliography, Lean modules,
and `COVERAGE.md`. The website generates its paper pages from those files.
The coverage map is the bridge from an article’s numbered statement to a
checked Lean declaration.

| Status | Meaning |
| --- | --- |
| Scaffold | The supplement has a structure; article results are not yet verified. |
| In progress | Consult individual coverage rows for completed and pending work. |
| Complete for stated scope | Every result in the explicitly recorded scope has been checked and matched to its source. |

A successful build checks the submitted Lean code. Empty namespaces and
imports can build successfully too, so build success is not a measure of
article coverage.

## Read the statement, including its hypotheses

For a verified result, follow the declaration link into the generated
reference. Inspect the type, the definitions it uses, and its assumptions.
Then compare it with the selected journal or arXiv version.

Extra regularity assumptions, excluded endpoints, changed coordinate
conventions, or a restricted parameter range belong in the coverage row.
Record them even when the proof itself is accepted by Lean.

## Inspect the axiom report

The article’s `Axioms.lean` is the place for `#print axioms` reports on its
final theorem declarations. Review the dependencies shown by Lean. Standard
foundational axioms and an unproved article-specific assumption have different
roles; the report should be read alongside the statement and scope.

The project treats warnings as errors, including Lean’s warnings for
unfinished `sorry` proofs. Every verified declaration also has a
`#assert_standard_axioms` check that rejects any transitive axiom outside
`propext`, `Classical.choice`, and `Quot.sound`. CI compares the coverage maps
with these assertions and the printed reports, and requires each advertised
theorem to appear in the generated Lean reference. Pending statements remain
in the coverage map until a proof is ready. The mathematical match to the
source statement still requires review.

## Reproduce the source snapshot

Each supplement page includes commands with a concrete commit. Clone the
whole project and check out that commit before building:

```sh
git clone https://github.com/Corrram/lean-verifications.git
cd lean-verifications
git checkout --detach <full-commit-from-the-supplement>
lake exe cache get
lake build
```

`lean-toolchain` pins Lean. `lake-manifest.json` pins the dependencies,
including copula and mathlib. Do not run `lake update` when reproducing a
published snapshot. The default build includes all Lean files under
`Papers/` and `Verification/`, including files not imported by a paper’s main module.

## Cite a stable supplement

Use the permanent article identifier and a full commit permalink. The latest
website is useful for browsing; its content changes as the project advances.
The commit link in the footer identifies the source of the deployed site.

The article DOI identifies the article. A software DOI, if one is issued for
an archived release, identifies the software. Keep these citations distinct
and describe the verified scope accurately.

## How this reference is generated

The handbook is built from Markdown and article metadata. A separate Lake
project pins [doc-gen4](https://github.com/leanprover/doc-gen4) to the release
matching the proof project’s Lean version. A generated import module includes
every local Lean file, so new papers enter the reference automatically.

The [Lean API](site:api/) includes the imported dependency modules and keeps
doc-gen4’s declaration search and source links. Search on this website also
reads that generated declaration index. Documentation generation does not
upgrade an article’s verification status.

Pushes to the main branch run the proof build and regenerate both parts of the
site before GitHub Pages deployment. Pull requests run the same checks without
publishing.
