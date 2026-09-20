# Coverage

**Status: in progress.** The moment identities in equation (28), reflection symmetry, convexity, and fixed-gamma interpolation are checked. The sign/magnitude construction and optimal boundary remain pending.

## Source and conventions

Source: [arXiv:2609.19890v1](https://arxiv.org/abs/2609.19890v1), 17 September 2026.

The pair is ordered (rho,gamma). Rho=12 E[UV]-3 and gamma=4 integral (C(t,t)+C(t,1-t)) dt-2. The moment formula proves gamma=2 E[abs(U+V-1)-abs(U-V)]. Reflection of the second coordinate negates both coefficients. The set-theoretic convexity and central-symmetry proofs apply to the actual attainable set, independently of any unproved boundary formula. The rest of Lemma 3.1, including signs, magnitudes, uniformity and its converse, remains pending.

## Result map

Proofs are in [Moments.lean](Moments.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Lemma 3.1, equation (28): moment identities | `Papers.AnsariRockelSteinmassl2026RhoGamma.moment_representation` | verified | All copulas; equation (29) and the converse construction are excluded from this row. |
| Theorem 1.1 proof: one-coordinate reflection | `Papers.AnsariRockelSteinmassl2026RhoGamma.reflection_pair` | verified | Second-coordinate reflection negates rho and gamma. |
| Theorem 1.1 proof: fixed-gamma interpolation | `Papers.AnsariRockelSteinmassl2026RhoGamma.fixed_gamma_intermediate` | verified | Supplied copulas share gamma and bracket the target rho; no optimal-boundary assertion. |
| Theorem 1.1: convexity of the attainable set | `Papers.AnsariRockelSteinmassl2026RhoGamma.region_convex` | verified | Actual coefficient range over all bivariate copulas. |
| Theorem 1.1: central symmetry of the attainable set | `Papers.AnsariRockelSteinmassl2026RhoGamma.region_centrally_symmetric` | verified | Every attainable (rho,gamma) has attainable (-rho,-gamma). |
| Lemma 3.1 beyond equation (28) and Lemma 3.2 | — | pending | Uniform magnitudes, sign decomposition and the converse coupling construction. |
| Theorem 1.1: exact boundary and its regularity | — | pending | Transport optimality, boundary attainment, junctions, limits, compactness and strict monotonicity. |
| Further consequences | — | pending | Maximal separation and sign thresholds. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
