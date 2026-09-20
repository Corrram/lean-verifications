# Coverage

**Status: in progress.** The derivative conventions, endpoint cases, entire xi=1 boundary, and the general SI/SD inequality xi<=abs(rho) are checked. Theorem 2 equality cases outside FGM, the curved diagonal-band boundary, and the full interior region remain pending.

## Source and conventions

Source: [arXiv:2506.15897v3](https://arxiv.org/abs/2506.15897v3), 19 May 2026.
Journal reference: [DOI 10.1016/j.jmva.2026.105630](https://doi.org/10.1016/j.jmva.2026.105630); version comparison pending.

Xi conditions coordinate 1 on coordinate 0. Equation (3) is matched to the conditional-CDF definition by the almost-everywhere derivative theorem, without a density assumption. FGM uses the full signed parameter interval [-1,1]. CI and CD in the FGM classification assert conditional monotonicity in both directions, so in particular include the direction used by the source. Within this family the equality case is exactly parameter zero. The general SI/SD inequality is proved separately in StochasticBounds.lean; its full equality classification remains pending. The proof constructs an antitone conditional-CDF version from concavity and compares squared differences with absolute differences. This is an alternative to the source maximum-principle proof, without a density assumption.

For the vertical boundary, a centered countermonotonic block with identity outside has xi=1 and rho=1-2 alpha^3. Varying alpha over [0,1] realizes the entire rho interval. This does not assert the source's diagonal-band formulas for 0<xi<1.

## Result map

Proofs are in [SelectedResults.lean](SelectedResults.lean), [RightBoundary.lean](RightBoundary.lean), and [StochasticBounds.lean](StochasticBounds.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Equation (3): derivative convention | `Papers.AnsariRockel2026XiRho.xi_derivative_formula` | verified | All bivariate copulas; constant extension of CDF sections outside [0,1]; endpoints have zero measure. |
| Theorem 1: xi=0 endpoint | `Papers.AnsariRockel2026XiRho.xi_zero_slice` | verified | Xi=0 characterizes independence and hence rho=0; no interior boundary is claimed. |
| Theorem 1: rho=+1 or -1 endpoints | `Papers.AnsariRockel2026XiRho.rho_extreme_implies_xi_one` | verified | All bivariate copulas; extremal rho implies xi=1. |
| Theorem 2: FGM subclass correspondence | `Papers.AnsariRockel2026XiRho.fgm_stochastically_monotone` | verified | Every FGM copula with abs(theta)<=1 is CI or CD. |
| Theorem 2: inequality restricted to FGM | `Papers.AnsariRockel2026XiRho.fgm_xi_le_abs_rho` | verified | Only the signed FGM family, including both parameter endpoints. |
| Theorem 2: equality restricted to FGM | `Papers.AnsariRockel2026XiRho.fgm_xi_eq_abs_rho_iff` | verified | Within FGM, xi=abs(rho) iff theta=0. The general equality characterization is pending. |
| Theorem 1: entire vertical boundary at xi=1 | `Papers.AnsariRockel2026XiRho.xi_one_slice`; `Papers.AnsariRockel2026XiRho.symmetric_xi_one_attained` | verified | Every rho in [-1,1] is attained with xi=1, even by a radially symmetric copula. Constructed centered W blocks and a proved continuous rho path supply all witnesses. |
| Theorem 1: curved boundary and interior region | — | pending | Construct the diagonal-band family, prove its coefficient formulas, global bounds, uniqueness and interior attainment. The full xi=1 slice is checked above. |
| Corollary 1: sharp global gap 0.4 | — | pending | Prove the universal bound and unique maximizer. |
| Equation (7): weighted conditional-CDF and derivative formulas | `Papers.AnsariRockel2026XiRho.rho_conditionalCDF_formula`; `Papers.AnsariRockel2026XiRho.rho_derivative_formula` | verified | Every bivariate copula, including singular laws; rho=12 times the integral of (1-u) times the first conditional CDF or CDF-section derivative, minus 3. |
| Theorem 2: general SI/SD inequality | `Papers.AnsariRockel2026XiRho.si_xi_le_rho`; `Papers.AnsariRockel2026XiRho.sd_xi_le_neg_rho`; `Papers.AnsariRockel2026XiRho.stochastic_xi_le_abs_rho` | verified | For every SI copula xi<=rho, and for every SD copula xi<=-rho; either class satisfies xi<=abs(rho). No family or density restriction. |
| Remark 1(d): obstruction to stochastic monotonicity | `Papers.AnsariRockel2026XiRho.not_stochastically_monotone_of_abs_rho_lt_xi` | verified | If xi>abs(rho), the copula is neither SI nor SD. The separate regression-model interpretation is not formalized. |
| Theorem 2: full equality classification | — | pending | The inequality is proved above. Characterizing equality as exactly W, independence, or M for arbitrary SI/SD copulas remains pending; the FGM equality case is checked. |
| Journal/preprint correspondence | — | pending | Only arXiv v3 is mapped. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
