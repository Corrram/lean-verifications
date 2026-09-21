# Coverage

**Status: in progress.** Proposition 3.2 is fully checked for equal-width straight permutation shuffles, and equal diagonal grid coefficient/tail formulas are checked. Bernstein and arbitrary rectangular checkerboard/check-min/check-W constructors, grid interpolation, and deterministic uniform CDF convergence are now checked. General rank formulas, xi approximation bounds and statistical convergence remain pending.

## Source and conventions

Source: [arXiv:2505.08045v2](https://arxiv.org/abs/2505.08045v2), 22 May 2026.

The recursive construction has N=2^n equal diagonal cells, each with mass 1/N, and zero off-diagonal masses. The CDF recurrence uses clipped rescaling and holds on cell boundaries as well. Independence in each cell gives the checkerboard, M gives check-min, and W gives check-w. Thus the source matrix is Delta=I_N/N, 1/N^2=(1/4)^n, and tr(Delta^T Delta)=1/N=(1/2)^n. The proofs below include n=0 (one cell). The newer equalGrid construction covers every N=n+1 and also checks xi for the deterministic variants and tails for all three families. General-matrix coefficient formulas and checkerboard xi remain outside this subset; the arbitrary-matrix constructors are checked below.

The original dyadic declarations remain available. The equalGrid index n represents N=n+1 cells: recursively split off width 1/N and rescale the remaining N-1 equal cells. All formulas below state their diagonal-matrix restriction explicitly.

For Proposition 3.2, permutationShuffle n pi has N=n+1 equal-width increasing
segments, one in each row and column prescribed by pi. The finite-sum CDF
identifies the constructed copula on the entire closed square. Indices are
zero-based; the source conditions pi(1)=1 and pi(N)=N become pi(0)=0 and
pi(Fin.last n)=Fin.last n. The inversion count counts j<i with pi(j)>pi(i),
equivalent to the source after renaming the pair. No symmetry or involution
assumption is used. Functional dependence is proved with a measurable graph
map, and both tail statements establish existence as well as the limit value.

## Result map

Proofs are in [DyadicBlocks.lean](DyadicBlocks.lean), [EqualGrids.lean](EqualGrids.lean),
and [PermutationShuffles.lean](PermutationShuffles.lean), imported by
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
| Section 3.2: actual straight-shuffle copula | `Papers.Rockel2025Approximation.permutationShuffle_cdf` | verified | Uniform segment law with equal width 1/N, N=n+1, for every permutation; exact finite-sum CDF, including strip boundaries. |
| Proposition 3.2: Spearman's rho | `Papers.Rockel2025Approximation.permutationShuffle_rho` | verified | rho=1-6 sum_i (pi(i)-i)^2/N^3, for every positive N and every permutation. |
| Proposition 3.2: Kendall's tau | `Papers.Rockel2025Approximation.permutationShuffle_tau` | verified | tau=1-4 N_inv(pi)/N^2; no symmetry assumption on pi. |
| Proposition 3.2: Chatterjee's xi | `Papers.Rockel2025Approximation.permutationShuffle_xi` | verified | xi=1, via an explicit measurable functional witness for the constructed copula. |
| Proposition 3.2: lower tail | `Papers.Rockel2025Approximation.permutationShuffle_lower_tail` | verified | The lower tail limit exists and equals 1 exactly when the first strip is fixed, and 0 otherwise. Includes N=1. |
| Proposition 3.2: upper tail | `Papers.Rockel2025Approximation.permutationShuffle_upper_tail` | verified | The upper tail limit exists and equals 1 exactly when the last strip is fixed, and 0 otherwise. Includes N=1. |
| Proposition 3.1: Bernstein copulas | — | pending | The actual family and CDF are checked below; full rank-coefficient and tail formulas remain pending. |
| Proposition 3.3 outside the mapped equal diagonal case | — | pending | Arbitrary rectangular constructors are checked below. The checkerboard xi formula and coefficient/tail formulas outside Delta=I_N/N remain unproved here. |
| Corollary 3.4 and Theorems 4.2, 4.5 | — | pending | Xi approximation bounds and statistical convergence; preserve the revised source hypotheses. |
| Section 2 / Proposition 3.1: actual Bernstein construction | `Papers.Rockel2025Approximation.bernstein_cdf` | verified | Every source copula and positive rectangular degrees m,n; exact tensor Bernstein CDF on the whole square, including endpoints. |
| Section 2: Bernstein uniform approximation | `Papers.Rockel2025Approximation.bernstein_uniform_error`; `Papers.Rockel2025Approximation.bernstein_uniform_convergence` | verified | Explicit uniform error sqrt(1/(4m))+sqrt(1/(4n)) and uniform CDF convergence. This does not assert xi or statistical convergence. |
| Section 2.2 / Proposition 3.3: arbitrary rectangular constructors | `Papers.Rockel2025Approximation.rectangular_checkerboard_cdf`; `Papers.Rockel2025Approximation.rectangular_checkMin_cdf`; `Papers.Rockel2025Approximation.rectangular_checkW_cdf` | verified | Any admissible nonnegative cell matrix on positive, possibly nonuniform partitions. Actual measure-based copulas with the displayed CDFs; no diagonal restriction. |
| Section 2.2: exact grid interpolation | `Papers.Rockel2025Approximation.patchwork_grid_interpolation` | verified | Every grid vertex agrees with the source copula for arbitrary local copula fillings. |
| Section 2.2: deterministic uniform convergence | `Papers.Rockel2025Approximation.patchwork_uniform_convergence` | verified | Every local filling on refining uniform grids, simultaneously including checkerboard, check-min and check-W. Rank coefficient convergence requires separate arguments. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.

## Latest package integration

The dependency is pinned to copula commit
`5926399c46f83d307127fd34b3aa2e416c940786`. New proof modules: [Constructors.lean](Constructors.lean).
Every mapped declaration is compiled and transitively audited against the standard
Lean axiom allowlist. Uniqueness of a numerical boundary value does not imply
uniqueness of its copula witness.
