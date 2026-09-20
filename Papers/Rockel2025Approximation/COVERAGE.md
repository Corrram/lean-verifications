# Coverage

**Status: in progress.** Proposition 3.3 rho/tau formulas are checked for every equal diagonal grid size, with check-min/check-w xi=1 and all three families' tail values. Arbitrary matrices, checkerboard xi, Bernstein formulas, and statistical convergence remain pending.

## Source and conventions

Source: [arXiv:2505.08045v2](https://arxiv.org/abs/2505.08045v2), 22 May 2026.

The recursive construction has N=2^n equal diagonal cells, each with mass 1/N, and zero off-diagonal masses. The CDF recurrence uses clipped rescaling and holds on cell boundaries as well. Independence in each cell gives the checkerboard, M gives check-min, and W gives check-w. Thus the source matrix is Delta=I_N/N, 1/N^2=(1/4)^n, and tr(Delta^T Delta)=1/N=(1/2)^n. The proofs below include n=0 (one cell). The newer equalGrid construction covers every N=n+1 and also checks xi for the deterministic variants and tails for all three families. Arbitrary matrices and checkerboard xi remain outside this subset.

The original dyadic declarations remain available. The equalGrid index n represents N=n+1 cells: recursively split off width 1/N and rescale the remaining N-1 equal cells. All formulas below state their diagonal-matrix restriction explicitly.

## Result map

Proofs are in [DyadicBlocks.lean](DyadicBlocks.lean) and [EqualGrids.lean](EqualGrids.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Section 2.2 / Proposition 3.3: diagonal-cell construction | `Papers.Rockel2025Approximation.dyadicBlocks_cdf` | verified | Exact recursive CDF for every depth, component copula and point of the closed square. |
| Supporting lemma for Proposition 3.3(i): rho block identity on diagonal dyadic grids | `Papers.Rockel2025Approximation.dyadicBlocks_rho` | verified | N=2^n identical diagonal components; rho=1-(1-rho(C))/N^2. |
| Supporting lemma for Proposition 3.3(ii): tau block identity on diagonal dyadic grids | `Papers.Rockel2025Approximation.dyadicBlocks_tau` | verified | N=2^n identical diagonal components; tau=1-(1-tau(C))/N. |
| Proposition 3.3(i)-(ii): checkerboard values | `Papers.Rockel2025Approximation.checkerboard_rho_tau` | verified | Only Delta=I_N/N with N=2^n: rho=1-1/N^2, tau=1-1/N. |
| Proposition 3.3(i)-(ii): check-min corrections | `Papers.Rockel2025Approximation.checkMin_corrections` | verified | Same grids; corrections +1/N^2 for rho and +1/N for tau. |
| Proposition 3.3(i)-(ii): check-w corrections | `Papers.Rockel2025Approximation.checkW_corrections` | verified | Same grids; corrections -1/N^2 for rho and -1/N for tau. |
| Section 2.2 / Proposition 3.3: all positive diagonal grid sizes | `Papers.Rockel2025Approximation.equalGrid_cdf`; `Papers.Rockel2025Approximation.equalGrid_rho_tau` | verified | N=n+1 for every natural n, Delta=I_N/N. Exact recursive CDF and rho/tau block identities for arbitrary component copulas. |
| Proposition 3.3(i)-(ii): checkerboard values for all N | `Papers.Rockel2025Approximation.equal_checkerboard_rho_tau` | verified | On Delta=I_N/N: rho=1-1/N^2 and tau=1-1/N, including N=1. |
| Proposition 3.3(i)-(iii): check-min and check-w | `Papers.Rockel2025Approximation.equal_checkMin_coefficients`; `Papers.Rockel2025Approximation.equal_checkW_coefficients` | verified | On Delta=I_N/N: corrections +/-1/N^2 for rho and +/-1/N for tau; both deterministic variants have xi=1. |
| Proposition 3.3(iv): tails on equal diagonal grids | `Papers.Rockel2025Approximation.equal_checkerboard_tails`; `Papers.Rockel2025Approximation.equal_checkMin_tails`; `Papers.Rockel2025Approximation.equal_checkW_tails` | verified | Both tail limits exist; checkerboard and check-w have zero tails, check-min has tails one, for every N>=1. |
| Propositions 3.1-3.2: Bernstein and general straight shuffles | — | pending | Construct the families and establish the full coefficient and tail formulas. |
| Proposition 3.3 outside the mapped equal diagonal case | — | pending | Arbitrary rectangular matrices, the checkerboard xi formula, and coefficient/tail formulas outside Delta=I_N/N remain unproved here. |
| Corollary 3.4 and Theorems 4.2, 4.5 | — | pending | Xi approximation bounds and statistical convergence; preserve the revised source hypotheses. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
