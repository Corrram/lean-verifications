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

/-- The second Debye function on nonzero arguments, with the Table 6 normalization. -/
noncomputable def debyeTwo (θ : ℝ) : ℝ :=
  (2/θ^2)*(∫ t in (0:ℝ)..θ, t^2/(Real.exp t-1))

theorem integrable_debye_second_section {θ : ℝ} (hθ : θ≠0) :
    Integrable (fun v : I => (v:ℝ)^2/(Real.exp (θ*(v:ℝ))-1)) := by
  have hi : Integrable (fun v : I => (v:ℝ)*debyeKernel (θ*(v:ℝ))/θ) :=
    Copula.integrable_continuous_unit volume
      ((continuous_subtype_val.mul (continuous_debyeKernel.comp (by fun_prop))).div_const θ)
  apply hi.congr
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
  have hv' : (v:ℝ)≠0 := fun h => hv (Subtype.ext h)
  rw [debyeKernel_of_ne (mul_ne_zero hθ hv')]
  field_simp

theorem integral_debye_second_section {θ : ℝ} (hθ : θ≠0) :
    (∫ v : I, (v:ℝ)^2/(Real.exp (θ*(v:ℝ))-1))=debyeTwo θ/(2*θ) := by
  rw [Copula.integral_unitInterval (fun v => v^2/(Real.exp (θ*v)-1))]
  have he : (fun v : ℝ => v^2/(Real.exp (θ*v)-1))=
      fun v : ℝ => (1/θ^2)*((θ*v)^2/(Real.exp (θ*v)-1)) := by
    funext v
    field_simp
  rw [he,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun t : ℝ => t^2/(Real.exp t-1)) hθ]
  simp only [mul_zero,mul_one,smul_eq_mul,debyeTwo]
  field_simp

theorem debyeKernel_neg (x : ℝ) : debyeKernel (-x)=debyeKernel x+x := by
  by_cases hx : x=0
  · subst x; simp
  rw [debyeKernel_of_ne (neg_ne_zero.mpr hx),debyeKernel_of_ne hx,Real.exp_neg]
  have he : Real.exp x≠0 := Real.exp_ne_zero _
  have he1 : Real.exp x-1≠0 := by
    intro h
    exact hx (Real.exp_injective ((sub_eq_zero.mp h).trans Real.exp_zero.symm))
  have he2 : (Real.exp x)⁻¹-1≠0 := by
    intro h
    have hh : Real.exp x=1 := by simpa using sub_eq_zero.mp h
    exact he1 (sub_eq_zero.mpr hh)
  field_simp [he,he1,he2]
  have he3 : 1-Real.exp x≠0 := by intro h; apply he1; linarith
  field_simp [he3]
  ring

theorem debyeOne_kernel_integral {θ : ℝ} (hθ : θ≠0) :
    debyeOne θ=∫ v : I, debyeKernel (θ*(v:ℝ)) := by
  have he : (fun v : I => debyeKernel (θ*(v:ℝ))) =ᵐ[volume]
      fun v => θ*((v:ℝ)/(Real.exp (θ*(v:ℝ))-1)) := by
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    have hv' : (v:ℝ)≠0 := fun h => hv (Subtype.ext h)
    rw [debyeKernel_of_ne (mul_ne_zero hθ hv')]
    ring
  rw [integral_congr_ae he,integral_const_mul,integral_debye_section hθ]
  field_simp

theorem debyeTwo_kernel_integral {θ : ℝ} (hθ : θ≠0) :
    debyeTwo θ=∫ v : I, 2*(v:ℝ)*debyeKernel (θ*(v:ℝ)) := by
  have he : (fun v : I => 2*(v:ℝ)*debyeKernel (θ*(v:ℝ))) =ᵐ[volume]
      fun v => (2*θ)*((v:ℝ)^2/(Real.exp (θ*(v:ℝ))-1)) := by
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    have hv' : (v:ℝ)≠0 := fun h => hv (Subtype.ext h)
    rw [debyeKernel_of_ne (mul_ne_zero hθ hv')]
    ring
  rw [integral_congr_ae he,integral_const_mul,integral_debye_second_section hθ]
  field_simp

theorem debyeOne_neg {θ : ℝ} (hθ : θ≠0) : debyeOne (-θ)=debyeOne θ+θ/2 := by
  rw [debyeOne_kernel_integral (neg_ne_zero.mpr hθ),debyeOne_kernel_integral hθ]
  simp_rw [neg_mul,debyeKernel_neg]
  have hi : Integrable (fun v : I => debyeKernel (θ*(v:ℝ))) :=
    Copula.integrable_continuous_unit volume (continuous_debyeKernel.comp (by fun_prop))
  have hj : Integrable (fun v : I => θ*(v:ℝ)) := Copula.integrable_continuous_unit volume (by fun_prop)
  rw [integral_add hi hj,integral_const_mul,Copula.integral_unit_id]
  ring

theorem debyeTwo_neg {θ : ℝ} (hθ : θ≠0) : debyeTwo (-θ)=debyeTwo θ+2*θ/3 := by
  rw [debyeTwo_kernel_integral (neg_ne_zero.mpr hθ),debyeTwo_kernel_integral hθ]
  simp_rw [neg_mul,debyeKernel_neg,mul_add]
  have hi : Integrable (fun v : I => 2*(v:ℝ)*debyeKernel (θ*(v:ℝ))) :=
    Copula.integrable_continuous_unit volume ((by fun_prop : Continuous (fun v : I => 2*(v:ℝ))).mul
      (continuous_debyeKernel.comp (by fun_prop)))
  have hj : Integrable (fun v : I => 2*(v:ℝ)*(θ*(v:ℝ))) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  rw [integral_add hi hj]
  have he : (fun v : I => 2*(v:ℝ)*(θ*(v:ℝ)))=fun v : I => (2*θ)*(v:ℝ)^2 := by
    funext v; ring
  rw [he,integral_const_mul,Copula.integral_unit_pow]
  ring

end Verification
