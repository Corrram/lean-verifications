# Coverage

**Status: in progress.** Biaffinity of concordance and the fixed-footrule, fixed-beta interpolation step of Theorem 1.1 are checked. Boundary shuffles, ordinal spreading, and the full joint region remain pending.

## Source and conventions

Source: [arXiv:2607.12841v1](https://arxiv.org/abs/2607.12841v1), 14 July 2026.

Tau=4 integral C dC-1, footrule=6 integral C(t,t) dt-2, and beta=4 C(1/2,1/2)-1. The library writes Q(C,D)=4 integral C dD-1; symmetry of Q matches the argument order of equation (6). The two endpoint copulas in the interpolation theorem must already have the same footrule and beta. Pairwise bounds alone are not treated as joint attainability. Tau along a mixture is quadratic, not affine.

## Result map

Proofs are in [Mixtures.lean](Mixtures.lean), imported by
[Main.lean](Main.lean). [Axioms.lean](Axioms.lean) prints and enforces the
standard transitive axiom allowlist for every declaration below.

| Source result | Lean declaration | Status | Hypotheses and scope |
| --- | --- | --- | --- |
| Section 2, equation (6): biaffinity of Q | `Papers.OrendayLaresRockel2026TauFootruleBeta.concordance_mixture` | verified | Any four copulas and two closed-interval mixture weights; source argument order agrees by Q symmetry. |
| Section 4, proof of Theorem 1.1: continuity of tau | `Papers.OrendayLaresRockel2026TauFootruleBeta.tau_mixture_continuous` | verified | Any pair of copulas, including singular ones. |
| Section 4, proof of Theorem 1.1: fill a vertical fibre | `Papers.OrendayLaresRockel2026TauFootruleBeta.fixed_footrule_beta_intermediate` | verified | Supplied copulas share both footrule and beta and bracket the requested tau. No boundary existence is assumed implicitly. |
| Proposition 2.1 and equation (9) | — | pending | Known pairwise bounds and the centered ordinal-sum transformation formulas. |
| Lemma 3.1 and Section 3 shuffle families | — | pending | General shuffle tau formula and simultaneous boundary coefficient values. |
| Theorem 1.1 as a whole | — | pending | Construct the simultaneous endpoints and prove all region inequalities. |
| Corollaries 4.1-4.2 and Section 5 | — | pending | Joint-region geometry, projection and volume. |

The verified subset consists only of the explicitly mapped statements and
proof steps. Pending rows are not implied by a successful build. Numerical
experiments and plots are not counted as formal proofs.
