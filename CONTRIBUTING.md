# Contributing

Use focused imports, `autoImplicit = false`, and namespaces
`Papers.<PaperId>` for paper-specific declarations. Follow mathlib's naming and
proof style. Cite the source result and its version in theorem docstrings;
use descriptive declaration names and keep theorem numbers in `COVERAGE.md`.

Do not introduce `sorry`, `admit`, new axioms, or disable warning checks to make
a proof compile. Keep planned results in the coverage map until a proof is
available. Standard foundational axioms (`propext`, `Classical.choice`,
`Quot.sound`) are permitted. Before claiming a result is verified, inspect
`#print axioms` for that declaration, including its transitive dependencies.
Record any nonstandard trust assumptions explicitly; do not label such a result
verified under the standard foundation.

Prove generic copula results in `copula` when practical. A paper wrapper can
specialize an upstream theorem, but must state the hypotheses that match the
article. Do not infer full article coverage from an import or from a successful
build. Keep parameter endpoints, singular cases, normalizations, and additional
hypotheses visible in the coverage map.

Before submitting:

```sh
lake exe cache get
lake build
python scripts/check_verification.py
```

Update article metadata and coverage alongside the code. When changing
dependencies, update the toolchain if necessary, the dependency pin, and the
generated manifest together, then rebuild every paper. Previously published
commit permalinks continue to refer to the earlier environment.

Contributions are licensed under Apache 2.0; see [LICENSE](LICENSE).
