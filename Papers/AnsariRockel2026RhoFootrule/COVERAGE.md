# Coverage

**Status: in progress.** Lemma 3.2, the classical quadratic upper envelope, and the fixed-footrule interpolation step of Corollary 1.2 are checked. The sharp transport correction and boundary construction remain pending.

## Source and conventions

Source: [arXiv:2608.20176v1](https://arxiv.org/abs/2608.20176v1), 20 August 2026.

The copula is a probability measure with uniform marginals. Rho uses 12 E[UV]-3 and footrule uses 6 integral C(t,t) dt-2. The exact moment identities are rho=1-6 E[(U-V)^2] and footrule=1-3 E[abs(U-V)]. The quadratic envelope follows from nonnegativity of the centered second moment. It is the classical upper bound in equations (16)-(17), not the article's sharper piecewise optimal boundary. No absolute-continuity hypothesis is added.

## Result map

Proofs are in [Moments.lean](Moments.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Lemma 3.2 / equation (4): moment representation | `Papers.AnsariRockel2026RhoFootrule.moment_representation` | verified | Every bivariate copula, including singular couplings. |
| Section 1.2, equations (16)-(17): quadratic upper bound | `Papers.AnsariRockel2026RhoFootrule.quadratic_upper_bound` | verified | Rho<=1-(2/3)(1-footrule)^2 for every copula; no sharp correction or equality classification is claimed. |
| Proof of Corollary 1.2: fixed-footrule interpolation | `Papers.AnsariRockel2026RhoFootrule.fixed_footrule_intermediate` | verified | Supplied copulas have equal footrule and bracket the target rho; optimal endpoints remain to be constructed. |
| Theorem 1.1 and Sections 4-5 | — | pending | Construct the extremizers, dual potentials, sharp transport correction and uniqueness proof. |
| Corollary 1.2 as a whole | — | pending | Prove both sharp boundaries and their attainment. |
| Section 2 applications | — | pending | Finite rankings, mixability and Chatterjee/correlation-ratio consequences. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
