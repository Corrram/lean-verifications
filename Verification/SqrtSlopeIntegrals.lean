import Verification.RampIntegrals
import Copula.Dependence.Conditional

/-! # Integrable square-root derivatives, including the singular endpoint -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def sqrtSlope (b t : ℝ) : ℝ := b/Real.sqrt (2*b*t)

theorem sqrtSlope_nonneg {b : ℝ} (hb : 0 ≤ b) (t : ℝ) : 0 ≤ sqrtSlope b t :=
  div_nonneg hb (Real.sqrt_nonneg _)

private theorem sqrtSlope_deriv {b t : ℝ} (hb : 0 < b) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => Real.sqrt (2*b*x)) (sqrtSlope b t) t := by
  have hp : 0 < 2*b*t := by positivity
  convert (((hasDerivAt_id t).const_mul (2*b)).sqrt (ne_of_gt hp)) using 1
  all_goals dsimp [sqrtSlope]
  all_goals field_simp

theorem sqrtSlope_intervalIntegrable {b : ℝ} (hb : 0 < b) {v : ℝ} (hv : 0 ≤ v) :
    IntervalIntegrable (sqrtSlope b) volume 0 v := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (show ContinuousOn (fun x : ℝ => Real.sqrt (2*b*x)) (uIcc 0 v) by fun_prop)
  · intro t ht
    rw [min_eq_left hv, max_eq_right hv] at ht
    exact sqrtSlope_deriv hb ht.1
  · intro t _
    exact sqrtSlope_nonneg hb.le t

theorem integral_sqrtSlope {b : ℝ} (hb : 0 < b) {v : ℝ} (hv : 0 ≤ v) :
    (∫ t in (0 : ℝ)..v, sqrtSlope b t) = Real.sqrt (2*b*v) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hv
    (show ContinuousOn (fun x : ℝ => Real.sqrt (2*b*x)) (Icc 0 v) by fun_prop)
    (fun t ht => sqrtSlope_deriv hb ht.1) (sqrtSlope_intervalIntegrable hb hv)]
  simp

theorem sqrtSlope_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : I => sqrtSlope b v) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (sqrtSlope_intervalIntegrable hb zero_le_one)
  have h := (unitInterval.measurePreserving_coe.integrable_comp_emb
    unitInterval.measurableEmbedding_coe).2 hi
  simpa only [Function.comp_def] using h

theorem integral_sqrtSlope_Iic {b : ℝ} (hb : 0 < b) (v : I) :
    (∫ t in Iic v, sqrtSlope b (t : ℝ)) = Real.sqrt (2*b*(v : ℝ)) := by
  rw [Copula.integral_unit_Iic, integral_sqrtSlope hb v.property.1]

theorem sqrtSlope_reflection_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : I => sqrtSlope b (1-(v : ℝ))) := by
  have hi := (unitInterval.measurePreserving_symm.integrable_comp_emb
    unitInterval.symmMeasurableEquiv.measurableEmbedding).mpr (sqrtSlope_integrable hb)
  exact hi

theorem integral_sqrtSlope_reflection_Ioc {b : ℝ} (hb : 0 < b) (c v : I) (hcv : c ≤ v) :
    (∫ t in Ioc c v, sqrtSlope b (1-(t : ℝ))) =
      Real.sqrt (2*b*(1-(c : ℝ)))-Real.sqrt (2*b*(1-(v : ℝ))) := by
  have he := Copula.integral_Iic_add_Ioc_unit (sqrtSlope_reflection_integrable hb) hcv
  have hp (u : I) : (∫ t in Iic u, sqrtSlope b (1-(t : ℝ))) =
      Real.sqrt (2*b)-Real.sqrt (2*b*(1-(u : ℝ))) := by
    rw [Copula.integral_unit_Iic (fun t => sqrtSlope b (1-t)), intervalIntegral.integral_comp_sub_left]
    simp only [sub_zero]
    have hv : 0 ≤ 1-(u : ℝ) := by linarith [u.property.2]
    have hrest : IntervalIntegrable (sqrtSlope b) volume (1-(u : ℝ)) 1 :=
      (sqrtSlope_intervalIntegrable hb zero_le_one).mono_set (by
        rw [uIcc_of_le (by linarith [u.property.1] : 1-(u : ℝ) ≤ 1), uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hv le_rfl)
    have hadj := intervalIntegral.integral_add_adjacent_intervals
      (sqrtSlope_intervalIntegrable hb hv) hrest
    rw [integral_sqrtSlope hb hv, integral_sqrtSlope hb zero_le_one] at hadj
    simp only [mul_one] at hadj
    linarith
  rw [hp, hp] at he
  linarith

end Verification
