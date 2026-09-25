import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Copula.Rank.ConditionalCDF

open ProbabilityTheory MeasureTheory Set Filter
open scoped unitInterval Topology

namespace Verification

noncomputable def debyeKernel (x : ℝ) : ℝ := (dslope Real.exp 0 x)⁻¹

theorem continuous_debyeKernel : Continuous debyeKernel := by
  apply Continuous.inv₀
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x=0
    · subst x
      exact continuousAt_dslope_same.mpr (Real.differentiable_exp 0)
    · exact (continuousAt_dslope_of_ne hx).mpr Real.continuous_exp.continuousAt
  · intro x
    by_cases hx : x=0
    · subst x; simp
    · rw [dslope_of_ne _ hx,slope_def_field]
      simp only [sub_zero,Real.exp_zero]
      apply div_ne_zero _ hx
      intro h
      have hh := Real.exp_injective ((sub_eq_zero.mp h).trans Real.exp_zero.symm)
      exact hx hh

theorem debyeKernel_of_ne {x : ℝ} (hx : x≠0) : debyeKernel x=x/(Real.exp x-1) := by
  simp [debyeKernel,dslope_of_ne _ hx,slope_def_field]

theorem integrable_debye_section {θ : ℝ} (hθ : θ≠0) :
    Integrable (fun v : I => (v:ℝ)/(Real.exp (θ*(v:ℝ))-1)) := by
  have hi : Integrable (fun v : I => debyeKernel (θ*(v:ℝ))/θ) :=
    Copula.integrable_continuous_unit volume ((continuous_debyeKernel.comp (by fun_prop)).div_const θ)
  apply hi.congr
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
  have hv' : (v:ℝ)≠0 := fun h => hv (Subtype.ext h)
  rw [debyeKernel_of_ne (mul_ne_zero hθ hv')]
  field_simp

/-- The first Debye function on nonzero arguments, as normalized in Table 6. -/
noncomputable def debyeOne (θ : ℝ) : ℝ :=
  (1/θ)*(∫ t in (0:ℝ)..θ, t/(Real.exp t-1))

theorem integral_debye_section {θ : ℝ} (hθ : θ≠0) :
    (∫ v : I, (v:ℝ)/(Real.exp (θ*(v:ℝ))-1))=debyeOne θ/θ := by
  rw [Copula.integral_unitInterval (fun v => v/(Real.exp (θ*v)-1))]
  have he : (fun v : ℝ => v/(Real.exp (θ*v)-1))=
      fun v : ℝ => (1/θ)*((θ*v)/(Real.exp (θ*v)-1)) := by
    funext v
    field_simp
  rw [he,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t : ℝ => t/(Real.exp t-1)) hθ]
  simp only [mul_zero,mul_one,smul_eq_mul,debyeOne]
  ring

end Verification
