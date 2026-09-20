# Coverage

**Status: in progress.** Moment identities, the classical quadratic bound and its constant-displacement equality criterion, all discrete upper-bound contact points, and fixed-footrule interpolation are checked. The sharp correction between contact points, uniqueness, full boundary and applications remain pending.

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
| Section 1.2, equations (16)-(17): quadratic upper bound | `Papers.AnsariRockel2026RhoFootrule.quadratic_upper_bound` | verified | Rho<=1-(2/3)(1-footrule)^2 for every copula; the exact equality criterion and discrete attaining points are checked below; the sharper correction between contact points remains pending. |
| Proof of Corollary 1.2: fixed-footrule interpolation | `Papers.AnsariRockel2026RhoFootrule.fixed_footrule_intermediate` | verified | Supplied copulas have equal footrule and bracket the target rho; discrete upper endpoints are constructed below; the remaining sharp endpoints are pending. |
| Section 1.2, equations (16)-(22): exact variance defect | `Papers.AnsariRockel2026RhoFootrule.quadratic_defect`; `Papers.AnsariRockel2026RhoFootrule.quadratic_equality_iff` | verified | The quadratic upper bound is an equality iff abs(U-V)=(1-footrule)/3 almost surely; no symmetry or density assumption. |
| Section 1.2 / contact point N=1: half-turn witness | `Papers.AnsariRockel2026RhoFootrule.halfTurn_rho`; `Papers.AnsariRockel2026RhoFootrule.halfTurn_footrule` | verified | A genuine reflected ordinal-sum copula with rho=footrule=-1/2. |
| Theorem 1.1 / Proposition 1.6: every discrete contact point | `Papers.AnsariRockel2026RhoFootrule.contactCopula_coefficients`; `Papers.AnsariRockel2026RhoFootrule.contactCopula_maximizes_rho`; `Papers.AnsariRockel2026RhoFootrule.contactCopula_constant_displacement` | verified | For every N=n+1>=1, constructs footrule=1-3/(2N), rho=1-3/(2N^2), proves global maximality at that footrule, and abs(U-V)=1/(2N) almost surely. Uniqueness is not claimed. |
| Theorem 1.1 and Sections 4-5 beyond discrete contact points | — | pending | Construct the extremizers between contact points, dual potentials, sharp transport correction and uniqueness proof. |
| Corollary 1.2 as a whole | — | pending | Prove both sharp boundaries and their attainment. |
| Section 2 applications | — | pending | Finite rankings, mixability and Chatterjee/correlation-ratio consequences. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
