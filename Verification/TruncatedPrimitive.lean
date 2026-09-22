import Verification.DiagonalBand

/-! # Integrating an intercept primitive over a truncated unit-height band -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- Truncating the primitive between levels A and A+1 gives its unit clamp. -/
theorem integral_truncated_primitive {w a : I → ℝ} (hw : Integrable w)
    (ha : Monotone a) (hprim : ∀ v : I, (∫ t in Iic v, w t) = a v)
    (l r : I) (hlr : l ≤ r) (A : ℝ) (hl : a l = A) (hr : a r = A+1) (v : I) :
    (∫ t in Iic v, (Ioc l r).indicator w t) = unitClamp (a v-A) := by
  rw [setIntegral_indicator measurableSet_Ioc]
  have hset : Iic v ∩ Ioc l r = Ioc l (min r v) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
    tauto
  rw [hset]
  by_cases hvl : v ≤ l
  · rw [Ioc_eq_empty_of_le ((min_le_right _ _).trans hvl), setIntegral_empty]
    have hh := ha hvl
    rw [hl] at hh
    unfold unitClamp
    rw [max_eq_left (by linarith)]
    norm_num
  by_cases hrv : r ≤ v
  · rw [min_eq_left hrv]
    have he := Copula.integral_Iic_add_Ioc_unit hw hlr
    rw [hprim, hprim, hl, hr] at he
    have hh := ha hrv
    rw [hr] at hh
    unfold unitClamp
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
    linarith
  · rw [min_eq_right (le_of_not_ge hrv)]
    have he := Copula.integral_Iic_add_Ioc_unit hw (le_of_not_ge hvl)
    rw [hprim, hprim, hl] at he
    have h₁ := ha (le_of_not_ge hvl)
    have h₂ := ha (le_of_not_ge hrv)
    rw [hl] at h₁
    rw [hr] at h₂
    unfold unitClamp
    rw [max_eq_right (by linarith), min_eq_right (by linarith)]
    linarith

end Verification
