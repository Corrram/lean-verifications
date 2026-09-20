# Coverage

**Status: in progress.** The full sign-magnitude representation, arbitrary-law converse, sign-bound attainment and equality of the attained support and transport maxima are checked. Weak duality, contact certificates and the half-shift optimizer for s>=1 are checked. The remaining optimizer branches, glued potential, general strong duality and exact boundary remain pending.

## Source and conventions

Source: [arXiv:2609.19890v1](https://arxiv.org/abs/2609.19890v1), 17 September 2026.

The pair is ordered (rho,gamma). Rho=12 E[UV]-3 and gamma=4 integral (C(t,t)+C(t,1-t)) dt-2. The moment formula proves gamma=2 E[abs(U+V-1)-abs(U-V)]. Reflection of the second coordinate negates both coefficients. The set-theoretic convexity and central-symmetry proofs apply to the actual attainable set, independently of any unproved boundary formula. Both directions of the sign-magnitude representation are checked below. The converse accepts an arbitrary probability space and a measurable Boolean sign; true represents +1 and false represents -1. The joint law is recovered, with zero-magnitude events proved null.

## Result map

Proofs are in [Moments.lean](Moments.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Lemma 3.1, equation (28): moment identities | `Papers.AnsariRockelSteinmassl2026RhoGamma.moment_representation` | verified | All copulas; both directions of the sign-magnitude representation are checked separately below. |
| Theorem 1.1 proof: one-coordinate reflection | `Papers.AnsariRockelSteinmassl2026RhoGamma.reflection_pair` | verified | Second-coordinate reflection negates rho and gamma. |
| Theorem 1.1 proof: fixed-gamma interpolation | `Papers.AnsariRockelSteinmassl2026RhoGamma.fixed_gamma_intermediate` | verified | Supplied copulas share gamma and bracket the target rho; no optimal-boundary assertion. |
| Theorem 1.1: convexity of the attainable set | `Papers.AnsariRockelSteinmassl2026RhoGamma.region_convex` | verified | Actual coefficient range over all bivariate copulas. |
| Theorem 1.1: central symmetry of the attainable set | `Papers.AnsariRockelSteinmassl2026RhoGamma.region_centrally_symmetric` | verified | Every attainable (rho,gamma) has attainable (-rho,-gamma). |
| Lemma 3.1: uniform magnitudes | `Papers.AnsariRockelSteinmassl2026RhoGamma.rankMagnitude_uniform`; `Papers.AnsariRockelSteinmassl2026RhoGamma.magnitude_marginal` | verified | The map u to abs(2u-1) preserves uniform measure; both magnitudes under every copula are uniform. Their joint law defines magnitudeCopula. |
| Lemma 3.1, equation (29): pointwise identities and moments | `Papers.AnsariRockelSteinmassl2026RhoGamma.sign_product_identity`; `Papers.AnsariRockelSteinmassl2026RhoGamma.sign_min_magnitude_identity`; `Papers.AnsariRockelSteinmassl2026RhoGamma.sign_magnitude_rho`; `Papers.AnsariRockelSteinmassl2026RhoGamma.sign_magnitude_gamma` | verified | Rho=3 E[SAB] and gamma=2 E[S min(A,B)] under the original copula law; sign is zero on median lines. The converse is checked in the following rows. |
| Equation (30): supporting functional and magnitude bound | `Papers.AnsariRockelSteinmassl2026RhoGamma.supporting_functional`; `Papers.AnsariRockelSteinmassl2026RhoGamma.supporting_functional_le` | verified | Every copula with its actual magnitude law; both statements hold for every real multiplier t, hence in particular t>=0. |
| Lemma 3.3(i): weak duality | `Papers.AnsariRockelSteinmassl2026RhoGamma.transport_weak_duality` | verified | Any continuous feasible potential and any uniform-marginal copula; no optimizer or strong duality is assumed. |
| Lemma 3.3(ii): contact-set certificate | `Papers.AnsariRockelSteinmassl2026RhoGamma.transport_contact_value`; `Papers.AnsariRockelSteinmassl2026RhoGamma.transport_contact_optimal` | verified | Almost-everywhere contact proves the exact value, optimality over all couplings and optimality over all continuous feasible potentials. |
| Lemma 3.5, theta<=1: explicit dual potential | `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShiftPotential_zero`; `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShiftPotential_integral`; `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShiftPotential_feasible` | verified | s=1/theta>=1. The potential has the source formula, normalization and integrated value; its dual inequality holds on the whole square. |
| Lemma 3.5, theta<=1: potential regularity | `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShiftPotential_lipschitz`; `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShiftPotential_deriv_bound` | verified | Lipschitz constant s-1, with a derivative bound for the same formula extended to the real line. Includes s=1. |
| Lemma 3.5 and sufficient direction of Lemma 3.6 | `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShift_cost`; `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShift_optimal`; `Papers.AnsariRockelSteinmassl2026RhoGamma.halfShiftPotential_contact` | verified | The constructed half-turn copula attains cost 1/4-s/2 and potential equality almost everywhere; it is globally optimal for s>=1. Nonoptimality for s<1 is not claimed. |
| Lemma 3.1 converse: complete joint-law realization | `Papers.AnsariRockelSteinmassl2026RhoGamma.signCopula_joint_law`; `Papers.AnsariRockelSteinmassl2026RhoGamma.signCopula_magnitude_law` | verified | Any probability space with two measurable uniform magnitudes and an arbitrary measurable sign, including conditional randomness. The constructed copula recovers the joint magnitude/sign law, not only its moments; zero magnitudes are null. |
| Lemma 3.1 converse: coefficient identities | `Papers.AnsariRockelSteinmassl2026RhoGamma.signCopula_rho`; `Papers.AnsariRockelSteinmassl2026RhoGamma.signCopula_gamma` | verified | The constructed copula has rho=3 E[SAB] and gamma=2 E[S min(A,B)] under the supplied law. |
| Lemma 3.2: sign-bound attainment | `Papers.AnsariRockelSteinmassl2026RhoGamma.signOptimizer_magnitude`; `Papers.AnsariRockelSteinmassl2026RhoGamma.signOptimizer_value`; `Papers.AnsariRockelSteinmassl2026RhoGamma.sign_bound_attained` | verified | For every magnitude copula D and every real t, an explicit sign choice produces a copula with magnitude law D and supporting value 3 integral c_t dD. |
| Equation (32): equivalence of optimization bounds | `Papers.AnsariRockelSteinmassl2026RhoGamma.supporting_bound_iff_transport_bound`; `Papers.AnsariRockelSteinmassl2026RhoGamma.transport_optimizer_lifts` | verified | Every real t; equivalent upper-bound problems, and every optimal magnitude coupling yields an optimal copula. |
| Equations (31)-(32): existence and equality of attained maxima | `Papers.AnsariRockelSteinmassl2026RhoGamma.transportValue_attained`; `Papers.AnsariRockelSteinmassl2026RhoGamma.supporting_maximum` | verified | Uniform-marginal measures form a weakly compact set and the cost is continuous. Both maxima exist, and the support maximum is exactly three times the independently defined transport supremum; no optimizer is assumed. |
| Lemma 3.3(ii): attained supporting-line certificate | `Papers.AnsariRockelSteinmassl2026RhoGamma.transport_contact_support` | verified | Any continuous feasible potential and supplied magnitude copula with almost-everywhere contact give a universal supporting bound and a constructed copula attaining it. |
| Theorem 1.1: exact boundary and its regularity | — | pending | Transport optimality, boundary attainment, junctions, limits, compactness and strict monotonicity. |
| Further consequences | — | pending | Maximal separation and sign thresholds. |
| Remark 3.4: general strong duality | — | pending | Equality with the dual infimum for every t>0 without a supplied contact certificate. |
| Lemmas 3.5-3.7 beyond the checked half-shift branch | — | pending | Nontrivial rho-footrule optimizer and potential, failure of half-shift optimality for s<1, and parameter estimates. |
| Definition 3.8, Proposition 3.9 and Lemma 4.1 | — | pending | General extremizer construction, its coefficients and the globally feasible glued dual potential. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.

Additional proof modules: [SignMagnitude.lean](SignMagnitude.lean), [Transport.lean](Transport.lean), [HalfShift.lean](HalfShift.lean), [SignConverse.lean](SignConverse.lean), [SignAttainment.lean](SignAttainment.lean).
