# Coverage

**Status: in progress.** Propositions 3.1-3.3 and Corollary 3.4 are fully checked: Bernstein formulas, permutation shuffles, all rectangular patchwork ranks and tails, and xi approximation bounds. Constructors and uniform CDF approximation are checked. The quadratic majorization step, estimator range and vanishing correction are checked. The MTP2 comparison in Theorem 4.2 and the sampled-checkerboard consistency and complexity claims in Theorem 4.5 remain pending.

## Source and conventions

Source: [arXiv:2505.08045v2](https://arxiv.org/abs/2505.08045v2), 22 May 2026.

The recursive construction has N=2^n equal diagonal cells, each with mass 1/N, and zero off-diagonal masses. The CDF recurrence uses clipped rescaling and holds on cell boundaries as well. Independence in each cell gives the checkerboard, M gives check-min, and W gives check-w. Thus the source matrix is Delta=I_N/N, 1/N^2=(1/4)^n, and tr(Delta^T Delta)=1/N=(1/2)^n. The proofs below include n=0 (one cell). The newer equalGrid construction covers every N=n+1 and also checks xi for the deterministic variants and tails for all three families. RectangularRanks and RectangularXi remove the diagonal restriction for all three rank coefficients and the xi error bound. RectangularTails also checks every general-matrix tail formula.

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
[BernsteinRho.lean](BernsteinRho.lean), [BernsteinRank.lean](BernsteinRank.lean), [BernsteinKendall.lean](BernsteinKendall.lean), [BernsteinExact.lean](BernsteinExact.lean),
[RectangularRanks.lean](RectangularRanks.lean), [RectangularXi.lean](RectangularXi.lean), [RectangularTails.lean](RectangularTails.lean), [ConvergenceSteps.lean](ConvergenceSteps.lean), and [PermutationShuffles.lean](PermutationShuffles.lean), imported by
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
| Proposition 3.1: complete Bernstein formulas | `Papers.Rockel2025Approximation.bernstein_all_coefficients` | verified | Rho, the exact tau and xi trace formulas, and both zero tail limits in one theorem, for every source copula and all positive rectangular degrees. Includes the printed piecewise Upsilon entries and Theta corner convention. |
| Theorems 4.2, 4.5 | — | pending | MTP2 checkerboard lower bound, statistical convergence and computational complexity; preserve the revised source hypotheses. |
| Section 2 / Proposition 3.1: actual Bernstein construction | `Papers.Rockel2025Approximation.bernstein_cdf` | verified | Every source copula and positive rectangular degrees m,n; exact tensor Bernstein CDF on the whole square, including endpoints. |
| Section 2: Bernstein uniform approximation | `Papers.Rockel2025Approximation.bernstein_uniform_error`; `Papers.Rockel2025Approximation.bernstein_uniform_convergence` | verified | Explicit uniform error sqrt(1/(4m))+sqrt(1/(4n)) and uniform CDF convergence. This does not assert xi or statistical convergence. |
| Section 2.2 / Proposition 3.3: arbitrary rectangular constructors | `Papers.Rockel2025Approximation.rectangular_checkerboard_cdf`; `Papers.Rockel2025Approximation.rectangular_checkMin_cdf`; `Papers.Rockel2025Approximation.rectangular_checkW_cdf` | verified | Any admissible nonnegative cell matrix on positive, possibly nonuniform partitions. Actual measure-based copulas with the displayed CDFs; no diagonal restriction. |
| Section 2.2: exact grid interpolation | `Papers.Rockel2025Approximation.patchwork_grid_interpolation` | verified | Every grid vertex agrees with the source copula for arbitrary local copula fillings. |
| Section 2.2: deterministic uniform convergence | `Papers.Rockel2025Approximation.patchwork_uniform_convergence` | verified | Every local filling on refining uniform grids, simultaneously including checkerboard, check-min and check-W. Rank coefficient convergence requires separate arguments. |
| Proposition 3.1: Bernstein basis integral | `Papers.Rockel2025Approximation.bernstein_basis_integral` | verified | Every degree n and index 0,...,n: integral 1/(n+1), proved by an explicit Bernstein antiderivative. |
| Proposition 3.1: rectangular Bernstein rho | `Papers.Rockel2025Approximation.bernstein_rho_grid`; `Papers.Rockel2025Approximation.bernstein_rho_frobenius` | verified | Every source copula and positive degrees m,n. Source indices 1,...,m and 1,...,n, with Gamma_ij=1/((m+1)(n+1)). |
| Proposition 3.1: Lambda entries | `Papers.Rockel2025Approximation.bernstein_lambda_entry` | verified | Integral of B_nj B_ns equals choose(n,j)choose(n,s)/((2n+1)choose(2n,j+s)); includes boundary and out-of-range indices. |
| Proposition 3.1: derivative Gram entries | `Papers.Rockel2025Approximation.bernstein_upsilon_entry` | verified | Exact derivative-basis product integral in a uniform binomial finite-difference form. Indices i,r denote source indices i+1,r+1. Equivalence with all source piecewise cases is checked by bernstein_upsilon_matrix below. |
| Proposition 3.1: actual Bernstein conditional CDF | `Papers.Rockel2025Approximation.bernstein_conditional_cdf` | verified | The finite polynomial derivative sum equals the actual conditional CDF almost everywhere in the conditioning coordinate, for every threshold. |
| Proposition 3.1: explicit rectangular Bernstein xi | `Papers.Rockel2025Approximation.bernstein_xi_finite_sum` | verified | Full finite contraction of grid-CDF entries and explicitly evaluated binomial Gram entries, for every positive m,n and every source copula. Uses uniform finite-difference Upsilon entries rather than the printed case split. |
| Proposition 3.1: both Bernstein tails | `Papers.Rockel2025Approximation.bernstein_lower_tail`; `Papers.Rockel2025Approximation.bernstein_upper_tail` | verified | Both limits exist and equal zero, for every source copula and every positive rectangular degree, via endpoint derivatives of the actual diagonal. |
| Proposition 3.1: Bernstein density | `Papers.Rockel2025Approximation.bernstein_density_nonnegative`; `Papers.Rockel2025Approximation.bernstein_density` | verified | Explicit mixed polynomial derivative, pointwise nonnegative, and equality of the actual copula measure to its density-weighted Lebesgue measure; arbitrary source copulas and positive rectangular degrees. |
| Proposition 3.1: conditional CDF monotonicity | `Papers.Rockel2025Approximation.bernstein_kernel_monotone` | verified | The continuous polynomial conditional CDF is monotone in the response threshold for every conditioning point, including endpoints. |
| Proposition 3.1: exact Theta entries | `Papers.Rockel2025Approximation.bernstein_theta_integral` | verified | The printed rational Theta entries equal twice the mixed derivative-basis integral. The last diagonal entry is exactly 1 under the source 0/0=1 convention. |
| Proposition 3.1: Bernstein Kendall tau | `Papers.Rockel2025Approximation.bernstein_tau_finite_sum`; `Papers.Rockel2025Approximation.bernstein_tau_trace` | verified | Both an evaluated finite sum and the exact source formula 1-tr(Theta_m D Theta_n D^T). Trace theorem indexes all positive degrees as m+1,n+1; no source-density or symmetry assumption. |
| Proposition 3.1: all printed Upsilon cases | `Papers.Rockel2025Approximation.bernstein_upsilon_matrix` | verified | Every derivative-product integral equals the source piecewise matrix, including the interior, last row, last column and last diagonal cases; degree one is included. |
| Proposition 3.1: Lambda matrix | `Papers.Rockel2025Approximation.bernstein_lambda_matrix` | verified | Exact matrix of Bernstein product integrals, using the printed binomial coefficients. |
| Proposition 3.1: exact Bernstein xi trace | `Papers.Rockel2025Approximation.bernstein_xi_trace` | verified | Exactly 6 tr(Upsilon D Lambda D^T)-2 using the printed piecewise Upsilon matrix, for all positive rectangular degrees and arbitrary source copulas. |

| Proposition 3.3(i): rectangular checkerboard rho | `Papers.Rockel2025Approximation.rectangular_checkerboard_rho` | verified | Exact Omega-weighted source formula for every positive m,n and every admissible cell matrix; no diagonal or symmetry restriction. |
| Proposition 3.3(i): check-min/check-W rho | `Papers.Rockel2025Approximation.rectangular_checkMin_rho`; `Papers.Rockel2025Approximation.rectangular_checkW_rho` | verified | Corrections +1/(mn) and -1/(mn), on every admissible uniform rectangular grid. |
| Proposition 3.3(ii): rectangular checkerboard tau | `Papers.Rockel2025Approximation.rectangular_checkerboard_tau` | verified | Exact 1-tr(Xi_m Delta Xi_n Delta^T), with Xi entries 2 below the diagonal, 1 on it and 0 above. Also valid on nonuniform partitions. |
| Proposition 3.3(ii): check-min/check-W tau | `Papers.Rockel2025Approximation.rectangular_checkMin_tau`; `Papers.Rockel2025Approximation.rectangular_checkW_tau` | verified | Corrections +/-tr(Delta^T Delta), including nonuniform partitions. |
| Supporting general patchwork rank identities | `Papers.Rockel2025Approximation.patchwork_rho_correction`; `Papers.Rockel2025Approximation.patchwork_tau_correction` | verified | Independent arbitrary local copulas in every cell, including singular laws. Rho correction is sum of mass times both cell widths times local rho; tau correction is sum of squared mass times local tau. Actual patchwork measure is proved equal to the weighted affine local laws. |

| Proposition 3.3(iii): actual conditional CDF | `Papers.Rockel2025Approximation.patchwork_conditionalCDF` | verified | The cellwise normalized kernel is the actual conditional CDF almost everywhere, with arbitrary local copulas and positive nonuniform partitions. Prefix integrals recover the actual patchwork CDF. |
| Proposition 3.3(iii): general finite xi formula | `Papers.Rockel2025Approximation.patchwork_xi_formula`; `Papers.Rockel2025Approximation.patchwork_xi_correction` | verified | Exact finite formula and checkerboard correction sum(width_j/width_i * mass_ij^2 * xi(C_ij)); singular and different local copulas are allowed. |
| Proposition 3.3(iii): checkerboard xi trace | `Papers.Rockel2025Approximation.rectangular_checkerboard_xi` | verified | Exactly (6m/n) tr(Delta^T Delta M_xi)-2 with M_xi=T T^T+T^T+I/3 and T strictly upper triangular; every admissible positive rectangular grid. |
| Proposition 3.3(iii): local perfect-dependence correction | `Papers.Rockel2025Approximation.uniform_patchwork_xi_correction`; `Papers.Rockel2025Approximation.rectangular_perfect_xi` | verified | Correction (m/n) tr(Delta^T Delta) when every local xi is one. The local copulas may differ across cells. Also proves the general local-xi weighted formula. |
| Proposition 3.3(iii): check-min/check-W xi | `Papers.Rockel2025Approximation.rectangular_checkMin_xi`; `Papers.Rockel2025Approximation.rectangular_checkW_xi` | verified | Both corrections equal (m/n) tr(Delta^T Delta), without diagonal or symmetry restrictions. |
| Corollary 3.4: rectangular xi error bound | `Papers.Rockel2025Approximation.rectangular_xi_error_bound` | verified | Absolute error at most m/n^2 for m<=n and 1/n otherwise; proved for every local copula filling, hence in particular every local perfect-dependence filling. |

| Proposition 3.3: both rectangular checkerboard tails | `Papers.Rockel2025Approximation.rectangular_checkerboard_lower_tail`; `Papers.Rockel2025Approximation.rectangular_checkerboard_upper_tail` | verified | Both limits exist and equal zero, for every positive rectangular grid and every admissible cell matrix. |
| Proposition 3.3: both rectangular check-min tails | `Papers.Rockel2025Approximation.rectangular_checkMin_lower_tail`; `Papers.Rockel2025Approximation.rectangular_checkMin_upper_tail` | verified | Both limits exist; coefficients are respectively the first and last corner masses times min(m,n). Lean natural indices encode all positive dimensions as m+1,n+1. |
| Proposition 3.3: both rectangular check-W tails | `Papers.Rockel2025Approximation.rectangular_checkW_lower_tail`; `Papers.Rockel2025Approximation.rectangular_checkW_upper_tail` | verified | Both limits exist and equal zero for every admissible rectangular matrix, with no diagonal or symmetry restriction. |

| Lemma 4.1: quadratic instance used in Theorem 4.2 | `Papers.Rockel2025Approximation.majorization_sum_sq` | verified | Finite decreasing comparison vector, dominance of all partial sums and equal total sums imply the square-sum inequality, by summation by parts. This row does not claim Karamata for arbitrary convex functions. |
| Equation (30): estimator as average and range | `Papers.Rockel2025Approximation.checkerboardEstimator_eq_average`; `Papers.Rockel2025Approximation.checkerboardEstimator_mem` | verified | The exact square-matrix estimator equals the mean of actual checkerboard and check-min xi values, and lies in [0,1], for every positive order. |
| Theorem 4.5 proof step: deterministic correction bound | `Papers.Rockel2025Approximation.checkerboardEstimator_correction_bounds` | verified | Estimator minus checkerboard xi lies between zero and 1/(2K), for every admissible K-by-K matrix. |
| Theorem 4.5 proof step: vanishing correction | `Papers.Rockel2025Approximation.checkerboardEstimator_correction_tendsto`; `Papers.Rockel2025Approximation.checkerboardEstimator_tendsto_iff` | verified | For any sequence of admissible matrices with order tending to infinity, the correction tends to zero, and estimator convergence is equivalent to checkerboard-xi convergence. This is a deterministic transfer theorem: sampled-checkerboard almost-sure consistency is not assumed proved. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.

## Latest package integration

The dependency is pinned to copula commit
`5926399c46f83d307127fd34b3aa2e416c940786`. New proof modules: [Constructors.lean](Constructors.lean).
Every mapped declaration is compiled and transitively audited against the standard
Lean axiom allowlist. Uniqueness of a numerical boundary value does not imply
uniqueness of its copula witness.
