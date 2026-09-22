import Papers.Rockel2026XiFootrule.TwoParameter
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Continuity and the limiting corner of the source parameter path -/

open ProbabilityTheory Set Verification Filter
open scoped Topology

namespace Papers.Rockel2026XiFootrule

/-- The explicit parameter path is continuous, including the regime switch at mu=2. -/
theorem twoParameter_parameters_continuous :
    Continuous diagonalHoleAlpha ∧ Continuous diagonalHoleBeta := by
  constructor
  · unfold diagonalHoleAlpha
    apply continuous_if_le continuous_id continuous_const (by fun_prop)
    · apply ContinuousOn.sub continuousOn_const
      apply ContinuousOn.div continuousOn_const (by fun_prop)
      intro x hx
      change 2 ≤ x at hx
      positivity
    · intro x hx
      change x = 2 at hx
      subst x
      norm_num
  · unfold diagonalHoleBeta
    fun_prop

/-- The path tends to the corner (1/2,1/2) as the real parameter tends to infinity. -/
theorem twoParameter_parameters_limit :
    Tendsto (fun μ : ℝ => (diagonalHoleAlpha μ,diagonalHoleBeta μ)) atTop
      (𝓝 ((1/2,1/2) : ℝ × ℝ)) := by
  have ha : Tendsto diagonalHoleAlpha atTop (𝓝 (1/2)) := by
    have h : Tendsto (fun μ : ℝ => 1/2-(2/5)/μ) atTop (𝓝 (1/2)) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun μ : ℝ => (2/5)*μ⁻¹) atTop (𝓝 ((2/5)*0)))
    apply h.congr'
    filter_upwards [eventually_gt_atTop (2:ℝ)] with μ hμ
    rw [diagonalHoleAlpha,ite_eq_right (not_le.mpr hμ)]
    congr 1
    field_simp
  have hb : Tendsto diagonalHoleBeta atTop (𝓝 (1/2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2:ℝ)] with μ hμ
    simp [diagonalHoleBeta,min_eq_right hμ]
    norm_num
  exact ha.prodMk_nhds hb

end Papers.Rockel2026XiFootrule
