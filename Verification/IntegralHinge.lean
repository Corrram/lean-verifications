import Copula.Rank.Integration

open MeasureTheory Set
open scoped unitInterval

namespace Verification

/-- Integral of a nonnegative linear hinge on the unit interval. -/
theorem integral_unit_linear_hinge (h : ℝ) (hh : 0 ≤ h) (t : I) :
    (∫ u : I, max 0 (h * ((u : ℝ) - (t : ℝ)))) =
      h * (1 - (t : ℝ)) ^ 2 / 2 := by
  rw [ProbabilityTheory.Copula.integral_unitInterval
    (fun u : ℝ => max 0 (h * (u - (t : ℝ))))]
  have hc : Continuous (fun u : ℝ => max 0 (h * (u - (t : ℝ)))) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := 0) (b := (t : ℝ)))
    (hc.intervalIntegrable (a := (t : ℝ)) (b := 1))]
  have hleft : (∫ u in (0 : ℝ)..(t : ℝ), max 0 (h * (u - (t : ℝ)))) = 0 := by
    have he : (∫ u in (0 : ℝ)..(t : ℝ), max 0 (h * (u - (t : ℝ)))) =
        ∫ _ in (0 : ℝ)..(t : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le t.property.1] at hu
      exact max_eq_left (mul_nonpos_of_nonneg_of_nonpos hh (sub_nonpos.mpr hu.2))
    rw [he, intervalIntegral.integral_const]
    simp
  have hright : (∫ u in (t : ℝ)..1, max 0 (h * (u - (t : ℝ)))) =
      h * (1 - (t : ℝ)) ^ 2 / 2 := by
    have he : (∫ u in (t : ℝ)..1, max 0 (h * (u - (t : ℝ)))) =
        ∫ u in (t : ℝ)..1, h * (u - (t : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le t.property.2] at hu
      exact max_eq_right (mul_nonneg hh (sub_nonneg.mpr hu.1))
    rw [he, intervalIntegral.integral_const_mul]
    change h * (∫ u in (t : ℝ)..1, (fun x : ℝ => x) u - (fun _ : ℝ => (t : ℝ)) u) =
      h * (1 - (t : ℝ)) ^ 2 / 2
    have hsub : (∫ u in (t : ℝ)..1, u - (t : ℝ)) =
        (∫ u in (t : ℝ)..1, u) - (∫ _ in (t : ℝ)..1, (t : ℝ)) := by
      simpa only using (intervalIntegral.integral_sub
        (f := fun u : ℝ => u) (g := fun _ : ℝ => (t : ℝ))
        (continuous_id.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _))
    rw [hsub, integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hleft, hright]
  ring

end Verification
