import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Equality in the finite quadratic mean inequality -/

open scoped BigOperators

namespace Verification

theorem finite_centered_square_sum (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) :
    (∑ i, (d i-(∑ j, d j)/(n : ℝ))^2) = (∑ i, d i^2)-(∑ i, d i)^2/(n : ℝ) := by
  let m := (∑ i, d i)/(n : ℝ)
  have he (i : Fin n) : (d i-m)^2 = d i^2-(2*m)*d i+m^2 := by ring
  change (∑ i, (d i-m)^2) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  dsimp [m]
  field_simp
  ring

theorem finite_cauchy_equality_iff (n : ℕ) (hn : 0 < n) (d : Fin n → ℝ) :
    (∑ i, d i^2)=(∑ i, d i)^2/(n : ℝ) ↔ ∀ i, d i=(∑ j, d j)/(n : ℝ) := by
  have he := finite_centered_square_sum n hn d
  constructor
  · intro h
    have hz : (∑ i, (d i-(∑ j, d j)/(n : ℝ))^2)=0 := by rw [he,h,sub_self]
    have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (d i-(∑ j, d j)/(n : ℝ)))).mp hz
    intro i
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp (hz' i (Finset.mem_univ i)))
  · intro h
    have hz : (∑ i, (d i-(∑ j, d j)/(n : ℝ))^2)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [h i,sub_self]
      norm_num
    rw [he] at hz
    exact sub_eq_zero.mp hz

end Verification
