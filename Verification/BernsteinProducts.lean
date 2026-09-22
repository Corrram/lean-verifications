import Verification.BernsteinIntegral

open MeasureTheory ProbabilityTheory Polynomial Set
open scoped unitInterval BigOperators

namespace Verification

/-- Product of Bernstein basis functions, including endpoint indices. -/
theorem bernstein_product (m n : ℕ) (i : Fin (m+1)) (j : Fin (n+1)) (u : I) :
    _root_.bernstein m i u * _root_.bernstein n j u =
      ((m.choose i : ℝ)*(n.choose j : ℝ)/(m+n).choose (i.val+j.val)) *
        _root_.bernstein (m+n) (i.val+j.val) u := by
  have hij : i.val+j.val ≤ m+n := by omega
  have hc : ((m+n).choose (i.val+j.val) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hij).ne'
  have hs : m+n-(i.val+j.val) = (m-i.val)+(n-j.val) := by omega
  simp only [_root_.bernstein_apply,hs,pow_add]
  field_simp

/-- Exact Gram matrix entry for Bernstein bases of arbitrary degrees. -/
theorem integral_bernstein_product (m n : ℕ) (i : Fin (m+1)) (j : Fin (n+1)) :
    (∫ u : I, _root_.bernstein m i u * _root_.bernstein n j u) =
      ((m.choose i : ℝ)*(n.choose j : ℝ))/
        (((m : ℝ)+(n : ℝ)+1)*(m+n).choose (i.val+j.val)) := by
  have hij : i.val+j.val < m+n+1 := by omega
  simp_rw [bernstein_product]
  rw [integral_const_mul,integral_bernstein (m+n) ⟨i.val+j.val,hij⟩]
  simp only [Nat.cast_add,div_eq_mul_inv,mul_inv_rev]
  ring

/-- The same formula also handles indices outside the basis, where the basis vanishes. -/
theorem integral_bernstein_product_nat (m n i j : ℕ) :
    (∫ u : I, _root_.bernstein m i u * _root_.bernstein n j u) =
      ((m.choose i : ℝ)*(n.choose j : ℝ))/
        (((m : ℝ)+(n : ℝ)+1)*(m+n).choose (i+j)) := by
  by_cases hi : i≤m
  · by_cases hj : j≤n
    · exact integral_bernstein_product m n ⟨i,by omega⟩ ⟨j,by omega⟩
    · have hj' : n < j := by omega
      simp [_root_.bernstein_apply,Nat.choose_eq_zero_of_lt hj']
  · have hi' : m < i := by omega
    simp [_root_.bernstein_apply,Nat.choose_eq_zero_of_lt hi']

end Verification
