import Verification.FrankConditional
import Verification.Debye

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval Topology

namespace Verification

private theorem frank_product_primitive (θ E Y u : ℝ) (hθ : θ≠0) (hY : 1-Y≠0)
    (hd : (Y-E)+(1-Y)*Real.exp (-θ*u)≠0) :
    HasDerivAt (fun x : ℝ => Y/(θ*(1-Y))*((1-E)/((Y-E)+(1-Y)*Real.exp (-θ*x))+
      Real.log ((Y-E)+(1-Y)*Real.exp (-θ*x))))
      (Real.exp (-θ*u)*Y*(1-Real.exp (-θ*u))*(1-Y)/((Y-E)+(1-Y)*Real.exp (-θ*u))^2) u := by
  have hx := ((hasDerivAt_id u).const_mul (-θ)).exp
  have hD := (hx.const_mul (1-Y)).const_add (Y-E)
  have hh := (((hasDerivAt_const u (1-E)).div hD hd).add (hD.log hd)).const_mul (Y/(θ*(1-Y)))
  convert hh using 1
  · funext x; rfl
  · dsimp only [Pi.mul_apply,Pi.add_apply,id_eq]
    field_simp [hθ,hY,hd]
    ring

theorem integral_frankPartial_product {θ : ℝ} (hθ : θ≠0) (v : I) (hv : (v:ℝ)≠0) :
    (∫ u : I, frankPartial θ u v*frankPartial θ v u)=
      1/θ-(v:ℝ)/(Real.exp (θ*(v:ℝ))-1) := by
  let E := Real.exp (-θ)
  let Y := Real.exp (-θ*(v:ℝ))
  have hY0 : Y≠0 := Real.exp_ne_zero _
  have hE : 1-E≠0 := frank_exp_den_ne_zero hθ
  have hY : 1-Y≠0 := by
    intro h
    have he : Real.exp (-θ*(v:ℝ))=Real.exp 0 := by simpa [Y] using (sub_eq_zero.mp h).symm
    have hh := Real.exp_injective he
    exact (mul_ne_zero (neg_ne_zero.mpr hθ) hv) hh
  let D : ℝ → ℝ := fun u => (Y-E)+(1-Y)*Real.exp (-θ*u)
  have hD (u : ℝ) : D u=frankDen θ u v := by dsimp [D,Y,E,frankDen]; ring
  have hd (u : ℝ) (hu : u∈Icc 0 1) : D u≠0 := by
    rw [hD]
    exact frankDen_ne_zero hθ (⟨u,hu⟩:I) v
  let F : ℝ → ℝ := fun u => Y/(θ*(1-Y))*((1-E)/D u+Real.log (D u))
  let f : ℝ → ℝ := fun u => Real.exp (-θ*u)*Y*(1-Real.exp (-θ*u))*(1-Y)/(D u)^2
  have hF (u : ℝ) (hu : u∈uIcc 0 1) : HasDerivAt F (f u) u :=
    frank_product_primitive θ E Y u hθ hY (hd u (by simpa using hu))
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by dsimp [D]; fun_prop)
    intro u hu
    exact pow_ne_zero 2 (hd u (by simpa using hu))
  have he : (fun u : I => frankPartial θ u v*frankPartial θ v u)=fun u : I => f (u:ℝ) := by
    funext u
    have hs : frankDen θ (v:ℝ) u=frankDen θ u v := by unfold frankDen; ring
    dsimp only [frankPartial,f]
    rw [hs,hD]
    dsimp only [Y]
    ring
  rw [he,Copula.integral_unitInterval f,intervalIntegral.integral_eq_sub_of_hasDerivAt hF hi]
  have hD0 : D 0=1-E := by dsimp [D]; simp
  have hD1 : D 1=Y*(1-E) := by dsimp [D,E]; simp only [mul_one]; ring
  dsimp only [F]
  rw [hD0,hD1,Real.log_mul hY0 hE]
  have hl : Real.log Y= -θ*(v:ℝ) := Real.log_exp _
  rw [hl]
  have hy : Real.exp (θ*(v:ℝ))=Y⁻¹ := by
    dsimp [Y]
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hy]
  have hy1 : Y⁻¹-1≠0 := by
    intro h
    have hh : Y=1 := by simpa using (sub_eq_zero.mp h)
    exact hY (sub_eq_zero.mpr hh.symm)
  field_simp [hθ,hY,hE,hY0,hy1]
  ring

theorem frank_kendallTau_of_cdf (C : Copula 2) {θ : ℝ} (hθ : θ≠0)
    (hc : ∀ u v : I, C.cdf ![u,v]=frankRealCDF θ u v) :
    C.kendallTau=1-4/θ*(1-debyeOne θ) := by
  rw [frank_kendallTau_integral_of_cdf C hθ hc]
  have he : (∫ v : I, ∫ u : I, frankPartial θ u v*frankPartial θ v u)=
      ∫ v : I, 1/θ-(v:ℝ)/(Real.exp (θ*(v:ℝ))-1) := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    exact integral_frankPartial_product hθ v (fun h => hv (Subtype.ext h))
  rw [he,integral_sub (integrable_const _) (integrable_debye_section hθ),
    integral_debye_section hθ]
  have hconst : (∫ _v : I, (1:ℝ)/θ)=1/θ := by simp
  rw [hconst]
  ring

end Verification
