import Papers.Rockel2026XiBlest.ExactRegion
import Verification.QuadraticTailDerivatives

/-! # The derivative identity for the whole positive parameter interval -/

open MeasureTheory ProbabilityTheory Set Filter Verification
open scoped unitInterval Topology

namespace Papers.Rockel2026XiBlest

theorem formula_tail (b : ℝ) (hb : 0 ≤ b) :
    xiFormula b=8*b^2*(7-3*b)/105+∫ p : I × I,xiTail b |squareDelta p| ∧
    nuFormula b=4*b*(28-9*b)/105+∫ p : I × I,nuTail b |squareDelta p| := by
  constructor
  · rw [← (extremal_coefficients b hb).1]
    exact quadraticBand_xi_tail b hb
  · rw [← (extremal_coefficients b hb).2,extremal_blest_noise,integral_noise_weighted_tail b hb]
    ring

noncomputable def boundaryDerivative (b : ℝ) : ℝ :=
  (112-72*b)/105+∫ p : I × I,6*|squareDelta p|^2*max 0 (b*|squareDelta p|-1)

theorem formula_hasDerivAt (b : ℝ) (hb : 0 < b) :
    HasDerivAt xiFormula (b*boundaryDerivative b) b ∧
    HasDerivAt nuFormula (boundaryDerivative b) b := by
  have hn : HasDerivAt (fun a : ℝ => 4*a*(28-9*a)/105) ((112-72*b)/105) b := by
    convert! ((((hasDerivAt_id b).const_mul 4).mul
      (((hasDerivAt_id b).const_mul 9).const_sub 28)).div_const 105) using 1
    simp only [id_eq]
    ring
  have hx : HasDerivAt (fun a : ℝ => 8*a^2*(7-3*a)/105) (b*((112-72*b)/105)) b := by
    convert! (((((hasDerivAt_id b).pow 2).const_mul 8).mul
      (((hasDerivAt_id b).const_mul 3).const_sub 7)).div_const 105) using 1
    simp only [id_eq,Pi.pow_apply]
    ring
  constructor
  · have h := hx.add (hasDerivAt_integral_xiTail b)
    have he : b*((112-72*b)/105)+b*(∫ p : I × I,6*|squareDelta p|^2*max 0 (b*|squareDelta p|-1)) =
        b*boundaryDerivative b := by unfold boundaryDerivative; ring
    rw [he] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hb] with a ha
    exact (formula_tail a ha.le).1
  · apply (hn.add (hasDerivAt_integral_nuTail b)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hb] with a ha
    exact (formula_tail a ha.le).2

/-- Lemma 4.5 / equation (7), including b=1. -/
theorem formula_derivative_identity (b : ℝ) (hb : 0 < b) :
    deriv nuFormula b=deriv xiFormula b/b := by
  rw [(formula_hasDerivAt b hb).1.deriv,(formula_hasDerivAt b hb).2.deriv]
  field_simp

theorem formula_zero_limits : Tendsto xiFormula (𝓝 0) (𝓝 0) ∧
    Tendsto nuFormula (𝓝 0) (𝓝 0) := by
  have hx : Continuous (fun b : ℝ => 8*b^2*(7-3*b)/105) := by fun_prop
  have hn : Continuous (fun b : ℝ => 4*b*(28-9*b)/105) := by fun_prop
  constructor
  · have h : Tendsto (fun b : ℝ => 8*b^2*(7-3*b)/105) (𝓝 0) (𝓝 0) := by
      simpa using hx.continuousAt.tendsto (x := 0)
    apply h.congr'
    filter_upwards [eventually_lt_nhds (show (0 : ℝ)<1 by norm_num)] with b hb
    simp only [xiFormula,ite_eq_left hb.le]
  · have h : Tendsto (fun b : ℝ => 4*b*(28-9*b)/105) (𝓝 0) (𝓝 0) := by
      simpa using hn.continuousAt.tendsto (x := 0)
    apply h.congr'
    filter_upwards [eventually_lt_nhds (show (0 : ℝ)<1 by norm_num)] with b hb
    simp only [nuFormula,ite_eq_left hb.le]

end Papers.Rockel2026XiBlest
