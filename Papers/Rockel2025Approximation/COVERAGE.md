# Coverage

**Status: in progress.** Rho and tau formulas in Proposition 3.3 are checked for diagonal dyadic grids, including their check-min and check-w corrections. General matrices, xi formulas, and convergence remain pending.

## Source and conventions

Source: [arXiv:2505.08045v2](https://arxiv.org/abs/2505.08045v2), 22 May 2026.

The recursive construction has N=2^n equal diagonal cells, each with mass 1/N, and zero off-diagonal masses. The CDF recurrence uses clipped rescaling and holds on cell boundaries as well. Independence in each cell gives the checkerboard, M gives check-min, and W gives check-w. Thus the source matrix is Delta=I_N/N, 1/N^2=(1/4)^n, and tr(Delta^T Delta)=1/N=(1/2)^n. The proofs below include n=0 (one cell). They do not claim formulas for arbitrary checkerboard matrices or the xi coefficient.

## Result map

Proofs are in [DyadicBlocks.lean](DyadicBlocks.lean), imported by
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
| Propositions 3.1-3.2: Bernstein and general straight shuffles | — | pending | Construct the families and establish the full coefficient and tail formulas. |
| Proposition 3.3 outside the mapped dyadic diagonal case | — | pending | General rectangular matrices, xi formulas and tail coefficients remain unproved here. |
| Corollary 3.4 and Theorems 4.2, 4.5 | — | pending | Xi approximation bounds and statistical convergence; preserve the revised source hypotheses. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
