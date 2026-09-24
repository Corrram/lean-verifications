import Verification.Nelsen22
import Mathlib.Analysis.Calculus.Deriv.Slope

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n22Angle (u v a : ℝ) : ℝ := Real.arcsin (1-u^a)+Real.arcsin (1-v^a)
noncomputable def n22Body (u v a : ℝ) : ℝ := 1-Real.sin (n22Angle u v a)

theorem n22Angle_deriv_zero {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (n22Angle u v) (-(Real.log u+Real.log v)) 0 := by
  have hd (x : ℝ) (hx : 0 < x) : HasDerivAt (fun a : ℝ => Real.arcsin (1-x^a)) (-Real.log x) 0 := by
    have hh : HasDerivAt (fun a : ℝ => 1-x^a) (-Real.log x) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).const_rpow hx).const_sub 1
    have ha := (Real.hasDerivAt_arcsin (x := 1-x^(0:ℝ)) (by simp) (by simp)).comp 0 hh
    simpa [Function.comp_def] using ha
  convert (hd u hu).add (hd v hv) using 1
  · rfl
  · ring

theorem n22Body_deriv_zero {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (n22Body u v) (Real.log u+Real.log v) 0 := by
  have hh := ((n22Angle_deriv_zero hu hv).sin).const_sub 1
  change HasDerivAt (fun a => 1-Real.sin (n22Angle u v a)) _ 0
  simpa [n22Angle,n22Body] using hh

theorem nelsen22_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ∈ Icc 0 1) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (nelsen22 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((independence 2).cdf ![u,v])) := by
  by_cases hu0 : u = 0
  · subst u; simp only [cdf_two_zero_left]; exact tendsto_const_nhds
  by_cases hv0 : v = 0
  · subst v
    have he (C : Copula 2) : C.cdf ![u,0] = 0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 (by simp)
    simp only [he]; exact tendsto_const_nhds
  have hu : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu0))
  have hv : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hv0))
  let F : ℝ → ℝ := fun a => Real.log (n22Body u v a)
  have hF : HasDerivAt F (Real.log (u:ℝ)+Real.log (v:ℝ)) 0 := by
    have hh := (n22Body_deriv_zero hu hv).log (by simp [n22Body,n22Angle])
    simpa [n22Body,n22Angle,F] using hh
  have hF0 : F 0 = 0 := by simp [F,n22Body,n22Angle]
  let Q := Function.update (fun a => F a/a) 0 (Real.log (u:ℝ)+Real.log (v:ℝ))
  have hQ : ContinuousAt Q 0 := by
    simpa only [hF0,sub_zero] using hF.continuousAt_div
  have he : Real.exp (Real.log (u:ℝ)+Real.log (v:ℝ)) = (independence 2).cdf ![u,v] := by
    rw [Real.exp_add,Real.exp_log hu,Real.exp_log hv,cdf_independence]
    simp
  have hl := (Real.continuous_exp.continuousAt.comp hQ).tendsto.comp ht
  simp only [Q,Function.comp_def,Function.update_self] at hl
  rw [he] at hl
  apply hl.congr'
  have ha : ∀ᶠ a in l, n22Angle u v (θ a) < Real.pi/2 :=
    ((n22Angle_deriv_zero hu hv).continuousAt.tendsto.comp ht).eventually
      (Iio_mem_nhds (by simp [n22Angle]; positivity))
  have hb : ∀ᶠ a in l, 0 < n22Body u v (θ a) :=
    ((n22Body_deriv_zero hu hv).continuousAt.tendsto.comp ht).eventually
      (Ioi_mem_nhds (by simp [n22Body,n22Angle]))
  filter_upwards [ha,hb] with a ha hb
  by_cases hz : θ a = 0
  · simp only [hz,Function.update_self,nelsen22_zero]
    exact he
  · rw [Function.update_of_ne hz,nelsen22_cdf_full (lt_of_le_of_ne (hθ a).1 (Ne.symm hz)) (hθ a).2]
    change Real.exp (Real.log (n22Body u v (θ a))/θ a) =
      (1-Real.sin (min (n22Angle u v (θ a)) (Real.pi/2)))^((θ a)⁻¹)
    rw [min_eq_left ha.le]
    change Real.exp (Real.log (n22Body u v (θ a))/θ a) = (n22Body u v (θ a))^((θ a)⁻¹)
    rw [Real.rpow_def_of_pos hb,div_eq_mul_inv]

theorem nelsen22_tendsto_positive_parameter {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ∈ Icc 0 1) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (nelsen22 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((nelsen22 η ⟨hη.le,hη1⟩).cdf ![u,v])) := by
  have hr (t : I) : ContinuousAt (fun x : ℝ => (t:ℝ)^x) η :=
    continuousAt_const.rpow continuousAt_id (Or.inr hη)
  have ha : ContinuousAt (fun x : ℝ => Real.arcsin (1-(u:ℝ)^x)+Real.arcsin (1-(v:ℝ)^x)) η :=
    (Real.continuous_arcsin.continuousAt.comp (continuousAt_const.sub (hr u))).add
      (Real.continuous_arcsin.continuousAt.comp (continuousAt_const.sub (hr v)))
  have hm : ContinuousAt (fun x : ℝ => min (Real.arcsin (1-(u:ℝ)^x)+Real.arcsin (1-(v:ℝ)^x)) (Real.pi/2)) η :=
    ha.min continuousAt_const
  have hb : ContinuousAt (fun x : ℝ => 1-Real.sin (min (Real.arcsin (1-(u:ℝ)^x)+Real.arcsin (1-(v:ℝ)^x)) (Real.pi/2))) η :=
    continuousAt_const.sub (Real.continuous_sin.continuousAt.comp hm)
  have hc : ContinuousAt (fun x : ℝ =>
      (1-Real.sin (min (Real.arcsin (1-(u:ℝ)^x)+Real.arcsin (1-(v:ℝ)^x)) (Real.pi/2)))^x⁻¹) η :=
    hb.rpow (continuousAt_id.inv₀ hη.ne') (Or.inr (inv_pos.mpr hη))
  rw [nelsen22_cdf_full hη hη1]
  apply (hc.tendsto.comp ht).congr'
  filter_upwards [ht.eventually (Ioi_mem_nhds hη)] with a ha
  rw [nelsen22_cdf_full ha (hθ a).2]
  rfl

theorem nelsen22_tendsto_parameter {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ∈ Icc 0 1) {η : ℝ} (hη : η ∈ Icc 0 1)
    (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (nelsen22 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((nelsen22 η hη).cdf ![u,v])) := by
  by_cases hz : η = 0
  · subst η
    rw [nelsen22_zero]
    exact nelsen22_tendsto_zero θ hθ ht u v
  · exact nelsen22_tendsto_positive_parameter θ hθ (lt_of_le_of_ne hη.1 (Ne.symm hz)) hη.2 ht u v

end Verification
