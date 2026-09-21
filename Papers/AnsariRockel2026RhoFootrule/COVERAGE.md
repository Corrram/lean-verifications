# Coverage

**Status: in progress.** The full exact region, both attained boundaries, the radical upper-boundary formulas, and the sharp minimal variance with its exact zero set are checked. Optimizer uniqueness, finite-ranking inequalities, and the xi/correlation-ratio applications remain pending.

## Source and conventions

Source: [arXiv:2608.20176v1](https://arxiv.org/abs/2608.20176v1), 20 August 2026.

The copula is a probability measure with uniform marginals. Rho uses 12 E[UV]-3 and footrule uses 6 integral C(t,t) dt-2. The exact moment identities are rho=1-6 E[(U-V)^2] and footrule=1-3 E[abs(U-V)]. The quadratic envelope follows from nonnegativity of the centered second moment. It is the classical upper bound in equations (16)-(17), not the article's sharper piecewise optimal boundary. No absolute-continuity hypothesis is added.

The contact family uses N equal diagonal blocks of a half-turn shuffle. Its coefficient values reach the universal quadratic bound, which proves global optimality at all discrete contact points without assuming the article's transport correction.

## Result map

Proofs are in [Moments.lean](Moments.lean) and [Touchpoints.lean](Touchpoints.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Lemma 3.2 / equation (4): moment representation | `Papers.AnsariRockel2026RhoFootrule.moment_representation` | verified | Every bivariate copula, including singular couplings. |
| Section 1.2, equations (16)-(17): quadratic upper bound | `Papers.AnsariRockel2026RhoFootrule.quadratic_upper_bound` | verified | Rho<=1-(2/3)(1-footrule)^2 for every copula; the equality criterion, discrete attaining points and sharp correction are checked below. |
| Proof of Corollary 1.2: fixed-footrule interpolation | `Papers.AnsariRockel2026RhoFootrule.fixed_footrule_intermediate` | verified | Supplied copulas have equal footrule and bracket the target rho; all sharp endpoints are constructed below. |
| Section 1.2, equations (16)-(22): exact variance defect | `Papers.AnsariRockel2026RhoFootrule.quadratic_defect`; `Papers.AnsariRockel2026RhoFootrule.quadratic_equality_iff` | verified | The quadratic upper bound is an equality iff abs(U-V)=(1-footrule)/3 almost surely; no symmetry or density assumption. |
| Section 1.2 / contact point N=1: half-turn witness | `Papers.AnsariRockel2026RhoFootrule.halfTurn_rho`; `Papers.AnsariRockel2026RhoFootrule.halfTurn_footrule` | verified | A genuine reflected ordinal-sum copula with rho=footrule=-1/2. |
| Theorem 1.1 / Proposition 1.6: every discrete contact point | `Papers.AnsariRockel2026RhoFootrule.contactCopula_coefficients`; `Papers.AnsariRockel2026RhoFootrule.contactCopula_maximizes_rho`; `Papers.AnsariRockel2026RhoFootrule.contactCopula_constant_displacement` | verified | For every N=n+1>=1, constructs footrule=1-3/(2N), rho=1-3/(2N^2), proves global maximality at that footrule, and abs(U-V)=1/(2N) almost surely. Uniqueness is not claimed. |
| Theorem 1.1: explicit upper-boundary copulas and their coefficients | `Papers.AnsariRockel2026RhoFootrule.boundary_coefficients`; `Papers.AnsariRockel2026RhoFootrule.upperRho_parameter` | verified | All left/right arcs and the endpoint. The upper boundary is selected from explicit arithmetic coordinates, not postulated as an optimizer. |
| Theorem 1.1: global sharp upper bound and attainment | `Papers.AnsariRockel2026RhoFootrule.sharp_upper_bound`; `Papers.AnsariRockel2026RhoFootrule.upper_boundary_attained` | verified | Every copula, including singular laws; every footrule in [-1/2,1], including all contact points and junctions. |
| Theorem 1.1, equation (9): closed radical formula | `Papers.AnsariRockel2026RhoFootrule.right_boundary_closed`; `Papers.AnsariRockel2026RhoFootrule.left_boundary_closed` | verified | Both halves of every interval, with delta=N(N+1)v^2 and the respective endpoint ell. The term delta*sqrt(delta) is delta^(3/2) on this nonnegative domain. |
| Corollary 1.2: sharp lower boundary and attainment | `Papers.AnsariRockel2026RhoFootrule.sharp_lower_bound`; `Papers.AnsariRockel2026RhoFootrule.lower_boundary_attained` | verified | The full interval [-1/2,1]; lower rho=-1+2(sqrt((1+2p)/3))^3, with actual attaining copulas. |
| Corollary 1.2: full exact region | `Papers.AnsariRockel2026RhoFootrule.exact_region` | verified | Necessary and sufficient conditions in the source order (rho,footrule); every intermediate rho is attained. |
| Theorem 1.1: agreement of boundary values at junctions | `Papers.AnsariRockel2026RhoFootrule.boundary_value_unique` | verified | Uniqueness of the boundary value. This is not a uniqueness theorem for optimizing copulas. |
| Proposition 1.6(i)-(ii): sharp dispersion bound and attainment | `Papers.AnsariRockel2026RhoFootrule.sharp_second_moment`; `Papers.AnsariRockel2026RhoFootrule.minimum_variance_attained` | verified | Every prescribed mean m in [0,1/2]. The variance correction is linked to the proved sharp boundary, and an actual copula attains it. |
| Proposition 1.6, equation (18): evaluated variance correction | `Papers.AnsariRockel2026RhoFootrule.right_variance_closed`; `Papers.AnsariRockel2026RhoFootrule.left_variance_closed` | verified | Both arc halves give 2*delta*sqrt(delta)/(3*sqrt(N(N+1)))-delta^2. |
| Proposition 1.6(iii): nonnegativity and exact zero set | `Papers.AnsariRockel2026RhoFootrule.minimum_variance_nonneg`; `Papers.AnsariRockel2026RhoFootrule.minimum_variance_zero_iff` | verified | Exactly m=0 or m=1/(2N) for a positive integer N. |
| Theorem 2.4: attainable constant magnitudes | `Papers.AnsariRockel2026RhoFootrule.constant_displacement_iff` | verified | Copula-law formulation: abs(U-V) is constant exactly at the stated means. The source centered-sum coordinates are Uprime=U-1/2 and Vprime=1/2-V. |
| Theorem 1.1: uniqueness of the optimizing copula | — | pending | The exact value and attainment are proved, but the contact-set rigidity needed to identify every optimizer is not yet checked. |
| Section 2 applications beyond the mapped dispersion/constant-value statements | — | pending | Finite-ranking inequalities and their discrete normalization; the full generalized-mixability optimization formulation; conditional-iid/Markov-product representations and xi/correlation-ratio consequences. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.

## Latest package integration

The dependency is pinned to copula commit
`5926399c46f83d307127fd34b3aa2e416c940786`. New proof modules: [ExactRegion.lean](ExactRegion.lean), [BoundaryFormula.lean](BoundaryFormula.lean), [Dispersion.lean](Dispersion.lean).
Every mapped declaration is compiled and transitively audited against the standard
Lean axiom allowlist. Uniqueness of a numerical boundary value does not imply
uniqueness of its copula witness.
