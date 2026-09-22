import Verification.ScaledRampMean

/-! # Evaluating the clamped-section CDF, including its boundary correction -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem integral_prefix_positive_ramp {b : ℝ} (hb : 0 < b) (a : ℝ) (u : I) :
    (∫ t in Iic u, max 0 (a-b*(t : ℝ))) =
      (max 0 a ^ 2-max 0 (a-b*(u : ℝ)) ^ 2)/(2*b) := by
  by_cases ha : a ≤ 0
  · have he (t : I) : max 0 (a-b*(t : ℝ)) = 0 := max_eq_left (by nlinarith [t.property.1])
    simp_rw [he]
    rw [max_eq_left ha]
    simp
  have ha0 : 0 ≤ a := (lt_of_not_ge ha).le
  rw [max_eq_right ha0]
  by_cases hau : a ≤ b*(u : ℝ)
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_positive_ramp hb ha0
      (by nlinarith [u.property.2]), max_eq_left (by linarith)]
    · ring
    · intro t ht
      have hut : (u : ℝ) ≤ t := le_of_lt (lt_of_not_ge ht)
      exact max_eq_left (by nlinarith)
  · have he : EqOn (fun t : I => max 0 (a-b*(t : ℝ))) (fun t => a-b*(t : ℝ)) (Iic u) := by
      intro t ht
      have htu : (t : ℝ) ≤ u := ht
      exact max_eq_right (by nlinarith)
    rw [setIntegral_congr_fun measurableSet_Iic he, Copula.integral_unit_Iic (fun t => a-b*t)]
    have hd (t : ℝ) : HasDerivAt (fun t => a*t-b*t^2/2) (a-b*t) t := by
      convert! (((hasDerivAt_id t).const_mul a).sub (((hasDerivAt_id t).pow 2).const_mul b |>.div_const 2)) using 1
      simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((show Continuous (fun t : ℝ => a-b*t) by fun_prop).intervalIntegrable _ _),
      max_eq_right (by linarith)]
    field_simp
    ring

theorem integral_prefix_clamp {b : ℝ} (hb : 0 < b) (a : ℝ) (u : I) :
    (∫ t in Iic u, unitClamp (a-b*(t : ℝ))) =
      (max 0 a^2-max 0 (a-b*(u : ℝ))^2-max 0 (a-1)^2+max 0 (a-1-b*(u : ℝ))^2)/(2*b) := by
  simp_rw [unitClamp_positive_parts, show ∀ t : I, a-b*(t : ℝ)-1 = a-1-b*(t : ℝ) from fun t => by ring]
  rw [integral_sub (Copula.integrable_continuous_unit (volume.restrict (Iic u)) (by fun_prop))
    (Copula.integrable_continuous_unit (volume.restrict (Iic u)) (by fun_prop)),
    integral_prefix_positive_ramp hb, integral_prefix_positive_ramp hb]
  ring

end Verification
