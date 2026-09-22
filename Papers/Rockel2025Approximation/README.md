# Measures of association for approximating copulas

**Marcus Rockel.** Preprint, first submitted 2025.

- Source version: [arXiv:2505.08045v2](https://arxiv.org/abs/2505.08045v2), 22 May 2026.
- Bibliography: [references.bib](references.bib); metadata: [paper.toml](paper.toml).

**Verification status: in progress.** Propositions 3.1-3.3 and Corollary 3.4 are fully checked: Bernstein formulas, permutation shuffles, all rectangular patchwork ranks and tails, and xi approximation bounds. Constructors and uniform CDF approximation are checked. The quadratic majorization step, estimator range and vanishing correction are checked. Theorem 4.2 is fully checked, including the MTP2-density implication and the actual checkerboard conditional integrals. Population checkerboard xi convergence and a quantitative CDF-error consistency criterion are checked for arbitrary copulas. The sampled-checkerboard almost-sure consistency and complexity claims in Theorem 4.5 remain pending.
See [COVERAGE.md](COVERAGE.md) for exact statements, restrictions and remaining work.

The permanent folder identifier is `Rockel2025Approximation`.

## Contents

- [Definitions.lean](Definitions.lean): article-specific definitions and notation.
- [DyadicBlocks.lean](DyadicBlocks.lean): checked statements and proof steps.
- [PermutationShuffles.lean](PermutationShuffles.lean): complete Proposition 3.2 for all positive orders and permutations.
- [EqualGrids.lean](EqualGrids.lean): rho, tau, deterministic xi and tails for every equal diagonal grid size.
- [BernsteinRank.lean](BernsteinRank.lean): rectangular Bernstein rho, finite-sum xi, conditional CDF, basis integrals and both tails.
- [BernsteinKendall.lean](BernsteinKendall.lean): actual Bernstein density and the exact Kendall tau trace formula.
- [BernsteinExact.lean](BernsteinExact.lean): complete Proposition 3.1, including the printed piecewise xi matrix.
- [RectangularRanks.lean](RectangularRanks.lean): complete rho and tau formulas for arbitrary rectangular matrices.
- [RectangularXi.lean](RectangularXi.lean): complete rectangular xi formulas and Corollary 3.4.
- [RectangularTails.lean](RectangularTails.lean): all six rectangular tail limits in Proposition 3.3.
- [CheckerboardMTP2.lean](CheckerboardMTP2.lean): full Theorem 4.2 and its stronger CI version.
- [PopulationConvergence.lean](PopulationConvergence.lean): population convergence, CDF stability and an explicit consistency criterion.
- [ConvergenceSteps.lean](ConvergenceSteps.lean): quadratic majorization, estimator range and vanishing correction.
- [Main.lean](Main.lean): entry point importing the final result modules.
- [Axioms.lean](Axioms.lean): axiom reports for the claimed final results.
- [COVERAGE.md](COVERAGE.md): source-result correspondence and remaining gaps.

## Reproduce

From the **repository root**, using the commit cited in the article:

```sh
lake exe cache get
lake build Papers.Rockel2025Approximation.Main
lake build
python scripts/check_verification.py
lake env lean Papers/Rockel2025Approximation/Axioms.lean
```

The full build checks all paper files. The final command prints the axiom
reports and rejects nonstandard transitive axioms. A successful build
does not mean that every statement in the article has been formalized.

## Citation

This folder is the supplement's stable landing page. Cite its full commit
permalink, the associated article, and any future software archive DOI as
described in [the publication guide](../../docs/PUBLISHING.md).
No supplement release or software DOI has been assigned yet.

## Exact-region package integration

- [Constructors.lean](Constructors.lean).
