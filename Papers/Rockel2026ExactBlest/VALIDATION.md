# Validation record

Source: arXiv:2609.27634v1, checked on 24 September 2026.
The downloaded TeX has SHA-256 `5004f7d396f865b09b1c6a06c7207ecdb0da00d5fdcd201168200c951247ac03`.

The arXiv TeX matches the sibling manuscript after removal of TeX comments
and blank lines. All 14 labeled mathematical results appear in COVERAGE.md.
The 23 imported modules match the original verification sources after
reversing only module-path and namespace changes. All 592 theorem statements
retain their explicit standard-axiom assertions. The coverage table advertises
166 declarations, also reported and asserted in Axioms.lean.

The independent SymPy 1.14.0 script passes all 82 exact identity checks.

The root coverage checker and its seven regression tests pass. The handbook
build and link/search checks pass for ten supplements and nineteen pages.
The shared dependency remains pinned to the root lake-manifest.json.

The full root `lake build` passed on 24 September 2026: 4,622 jobs,
with Lean 4.34.0 and copula revision
`72a596ebd8c111cb11a046be0d5c5cd64a878954`. This fresh Windows build includes
all 23 imported proof modules, their 592 standard-axiom assertions, and the
166 printed/asserted coverage declarations in Axioms.lean. It also recompiles
the existing papers against the shared Blest infrastructure. No Lean proof
changes were needed after migration.

The root checker passes for all 1,220 advertised declarations across ten
supplements. The toolchain, lakefile, and dependency manifest are unchanged.
The handbook preview was rebuilt and checked; a full doc-gen4 API rendering
was not run locally (its generated import index includes the new modules).
