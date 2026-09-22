import Verification.FoldedUniform
import Verification.ConditionalMean

/-! # Exact xi and correlation ratio of the folded-uniform model -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem foldKernel_square_integral (v : I) :
    (∫ u : I, foldKernel v u^2) = (unitClamp (2*(v : ℝ))+3*unitClamp (2*(v : ℝ)-1))/4 := by
  have he (u : I) : foldKernel v u^2 =
      (if foldLower u ≤ v then (1 : ℝ) else 0)/4+3*(if foldUpper u ≤ v then 1 else 0)/4 := by
    have hh : foldLower u ≤ foldUpper u := by
      change (1-(u : ℝ))/2 ≤ (1+(u : ℝ))/2
      linarith [u.property.1]
    unfold foldKernel
    split_ifs
    all_goals norm_num at *
    all_goals order
  simp_rw [he]
  rw [integral_add ((fold_indicator_integrable foldLower continuous_foldLower.measurable v).div_const 4)
    (((fold_indicator_integrable foldUpper continuous_foldUpper.measurable v).const_mul 3).div_const 4),
    integral_div, integral_div, integral_const_mul, fold_lower_integral, fold_upper_integral]
  ring

theorem foldedUniform_xi : foldedUniform.chatterjeeXi = 1/4 := by
  have he (v : I) : (∫ u : I, foldedUniform.conditionalCDF u v^2) =
      if (v : ℝ) ≤ 1/2 then (v : ℝ)/2 else 1-3*(1-(v : ℝ))/2 := by
    have hp : (fun u => foldedUniform.conditionalCDF u v^2) =ᵐ[volume] fun u => foldKernel v u^2 := by
      filter_upwards [foldedUniform_conditionalCDF v] with u hu
      rw [hu]
    rw [integral_congr_ae hp, foldKernel_square_integral]
    unfold unitClamp
    rw [max_eq_right (by nlinarith [v.property.1] : 0 ≤ 2*(v : ℝ))]
    by_cases h : (v : ℝ) ≤ 1/2
    · rw [ite_eq_left h, min_eq_right (by linarith), max_eq_left (by linarith)]
      norm_num
      ring
    · rw [ite_eq_right h, min_eq_left (by linarith), max_eq_right (by linarith), min_eq_right (by linarith [v.property.2])]
      ring
  unfold Copula.chatterjeeXi
  simp_rw [he]
  rw [integral_unit_two_halves (fun v : ℝ => v/2) (fun v : ℝ => 1-3*v/2) (by fun_prop) (by fun_prop)]
  have hd (v : ℝ) : HasDerivAt (fun v => v-v^2/2) (v/2+(1-3*v/2)) v := by
    convert! ((hasDerivAt_id v).sub (((hasDerivAt_id v).pow 2).div_const 2)) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hd v)
    ((show Continuous (fun v : ℝ => v/2+(1-3*v/2)) by fun_prop).intervalIntegrable _ _)]
  norm_num

theorem foldKernel_response_integral (u : I) : (∫ v : I, foldKernel v u) = 1/2 := by
  have hi (a : I) : Integrable (fun v : I => if a ≤ v then (1 : ℝ) else 0) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.ite (measurableSet_le measurable_const measurable_id) measurable_const).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun v => by split_ifs <;> norm_num
  unfold foldKernel
  rw [integral_add ((hi (foldLower u)).div_const 2) ((hi (foldUpper u)).div_const 2),
    integral_div, integral_div, Copula.integral_unit_upper_indicator, Copula.integral_unit_upper_indicator]
  dsimp [foldLower,foldUpper]
  ring

theorem foldedUniform_conditionalMean :
    conditionalMean foldedUniform =ᵐ[volume] fun _ => (1/2 : ℝ) := by
  have ha : ∀ᵐ u : I, ∀ᵐ v : I, foldedUniform.conditionalCDF u v = foldKernel v u :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v u : I => foldedUniform.conditionalCDF u v = foldKernel v u)
      (measurableSet_eq_fun foldedUniform.measurable_conditionalCDF foldKernel_measurable)).mp
      (Filter.Eventually.of_forall foldedUniform_conditionalCDF)
  filter_upwards [ha] with u hu
  rw [conditionalMean_eq, integral_congr_ae hu, foldKernel_response_integral]
  norm_num

theorem foldedUniform_correlationRatio : correlationRatio foldedUniform = 0 := by
  unfold correlationRatio
  have he : (fun u => (conditionalMean foldedUniform u-1/2)^2) =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [foldedUniform_conditionalMean] with u hu
    rw [hu]
    norm_num
  rw [integral_congr_ae he]
  simp

end Verification
