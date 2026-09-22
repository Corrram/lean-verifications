import Verification.BernsteinTauTrace

/-! # Proposition 3.1: the Bernstein density and exact Kendall trace formula -/

open MeasureTheory ProbabilityTheory Matrix
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

theorem bernstein_density_nonnegative (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n)
    (x : Fin 2 → I) : 0 ≤ Verification.bernsteinDensity C m n x :=
  Verification.bernsteinDensity_nonneg C m n hm hn x

theorem bernstein_density (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (Verification.bernsteinDensity C m n x)) :=
  Verification.toMeasure_bernstein_density C m n hm hn

theorem bernstein_kernel_monotone (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) (u : I) :
    Monotone (Verification.bernsteinKernel C m n u) :=
  Verification.bernsteinKernel_mono C m n hm hn u

theorem bernstein_theta_integral (k : ℕ) (i r : Fin (k+1)) :
    Verification.bernsteinThetaMatrix k i r =
      2 * (∫ u : I, Verification.bernsteinDerivative (k+1) (i.val+1) u *
        _root_.bernstein (k+1) (r.val+1) u) := by
  rw [Verification.integral_bernsteinDerivative_mul]
  exact Verification.bernsteinTheta_eq_mixedGram k i r

theorem bernstein_tau_finite_sum (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).kendallTau =
      4 * (∑ i : Fin m, ∑ j : Fin n, ∑ r : Fin m, ∑ s : Fin n,
        C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
        C.cdf ![_root_.bernstein.z r.succ,_root_.bernstein.z s.succ] *
        Verification.bernsteinMixedGram m i r * Verification.bernsteinMixedGram n j s) - 1 :=
  Verification.bernstein_tau_finite_sum C m n hm hn

/-- m,n index the positive degrees m+1,n+1; Theta includes the paper's exceptional corner. -/
theorem bernstein_tau_trace (C : Copula 2) (m n : ℕ) :
    (C.bernstein (m+1) (n+1) (by omega) (by omega)).kendallTau =
      1 - Matrix.trace (Verification.bernsteinThetaMatrix m * Verification.bernsteinGridMatrix C m n *
        Verification.bernsteinThetaMatrix n * (Verification.bernsteinGridMatrix C m n)ᵀ) :=
  Verification.bernstein_tau_trace C m n

end Papers.Rockel2025Approximation
