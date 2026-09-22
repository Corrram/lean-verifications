import Papers.Rockel2025Approximation.Constructors
import Verification.BernsteinRho

/-! # Proposition 3.1: the exact Bernstein Spearman-rho formula -/

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

/-- The boundary-zero rows/columns vanish, leaving the source indices 1,...,m and 1,...,n. -/
theorem bernstein_rho_grid (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (C.bernstein m n hm hn).spearmanRho =
      12*(∑ i : Fin m, ∑ j : Fin n, C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ])/
        (((m : ℝ)+1)*((n : ℝ)+1))-3 := by
  rw [Verification.bernstein_rho]
  have he : (∑ i : Fin (m+1), ∑ j : Fin (n+1), C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j]) =
      ∑ i : Fin m, ∑ j : Fin n, C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] := by
    rw [Fin.sum_univ_succ]
    simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_left,Finset.sum_const_zero,zero_add]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_succ]
    simp only [_root_.bernstein.z_zero,Copula.cdf_two_zero_right,zero_add]
  rw [he]

/-- The Frobenius form 12 tr(Gamma^T D)-3 with Gamma_ij=1/((m+1)(n+1)). -/
theorem bernstein_rho_frobenius (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (C.bernstein m n hm hn).spearmanRho =
      12*(∑ i : Fin m, ∑ j : Fin n, (1/(((m : ℝ)+1)*((n : ℝ)+1)))*
        C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ])-3 := by
  rw [bernstein_rho_grid]
  simp only [← Finset.mul_sum]
  ring

end Papers.Rockel2025Approximation
