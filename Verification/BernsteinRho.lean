import Verification.BernsteinIntegral
import Copula.Bernstein.Basic
import Copula.Rank.SpearmanCDF

/-! # Exact Spearman rho for arbitrary rectangular Bernstein copulas -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval BigOperators

namespace Verification

theorem bernstein_cdf_integral (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∫ x, (C.bernstein m n hm hn).cdf x ∂(Copula.independence 2).toMeasure) =
      (∑ i : Fin (m+1), ∑ j : Fin (n+1), C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j])/
        (((m : ℝ)+1)*((n : ℝ)+1)) := by
  have he (x : Fin 2 → I) : (C.bernstein m n hm hn).cdf x =
      ∑ i : Fin (m+1), ∑ j : Fin (n+1), C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j]*
        _root_.bernstein m i (x 0)*_root_.bernstein n j (x 1) := by
    rw [Copula.cdf_bernstein,Copula.bernsteinCDF_eq_sum]
  simp_rw [he]
  rw [integral_finsetSum]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      have h := Copula.integral_independence_mul
        (fun u => C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j]*_root_.bernstein m i u)
        (fun v => _root_.bernstein n j v)
      rw [h,integral_const_mul,integral_bernstein,integral_bernstein]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · intro j _
      exact Copula.integrable_continuous_cube _ (by fun_prop)
  · intro i _
    exact Copula.integrable_continuous_cube _ (by fun_prop)

/-- Frobenius sum form of Proposition 3.1; the zero-index terms vanish automatically. -/
theorem bernstein_rho (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (C.bernstein m n hm hn).spearmanRho =
      12*(∑ i : Fin (m+1), ∑ j : Fin (n+1), C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j])/
        (((m : ℝ)+1)*((n : ℝ)+1))-3 := by
  rw [Copula.spearmanRho_eq_integral_cdf,bernstein_cdf_integral]
  ring

end Verification
