import Verification.FrankTau
import Verification.CubeFubini
import Copula.Rank.SpearmanCDF
import Verification.ClampedRhoOptimization
import Verification.RampIntegrals

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval Topology

namespace Verification

private theorem frank_partial_primitive (θ E X v : ℝ) (hθ : θ≠0) (hX : 1-X≠0)
    (hXE : X-E≠0) (hd : (X-E)+(1-X)*Real.exp (-θ*v)≠0) :
    HasDerivAt (fun y : ℝ => X/(θ*(X-E))*(θ*y+(1-E)/(1-X)*
      Real.log ((X-E)+(1-X)*Real.exp (-θ*y))))
      (X*(1-Real.exp (-θ*v))/((X-E)+(1-X)*Real.exp (-θ*v))) v := by
  have hy := ((hasDerivAt_id v).const_mul (-θ)).exp
  have hD := (hy.const_mul (1-X)).const_add (X-E)
  have hh := (((hasDerivAt_id v).const_mul θ).add
    ((hD.log hd).const_mul ((1-E)/(1-X)))).const_mul (X/(θ*(X-E)))
  convert hh using 1
  · funext y; rfl
  · dsimp only [Pi.mul_apply,Pi.add_apply,id_eq]
    field_simp [hθ,hX,hXE,hd]
    have hd' : X-X*Real.exp (-(θ*v))-E+Real.exp (-(θ*v))≠0 := by
      convert hd using 1
      simp only [neg_mul]
      ring
    ring_nf
    field_simp [hd']
    linear_combination X * (mul_inv_cancel₀ hd')

theorem integral_frankPartial_second {θ : ℝ} (hθ : θ≠0) (u : I)
    (hu0 : (u:ℝ)≠0) (hu1 : (u:ℝ)≠1) :
    (∫ v : I, frankPartial θ u v)=
      Real.exp (-θ*(u:ℝ))/(Real.exp (-θ*(u:ℝ))-Real.exp (-θ))*
        (1-(u:ℝ)*(1-Real.exp (-θ))/(1-Real.exp (-θ*(u:ℝ)))) := by
  let E := Real.exp (-θ)
  let X := Real.exp (-θ*(u:ℝ))
  have hX0 : X≠0 := Real.exp_ne_zero _
  have hE : 1-E≠0 := frank_exp_den_ne_zero hθ
  have hX : 1-X≠0 := by
    intro h
    have he : Real.exp (-θ*(u:ℝ))=Real.exp 0 := by simpa [X] using (sub_eq_zero.mp h).symm
    exact (mul_ne_zero (neg_ne_zero.mpr hθ) hu0) (Real.exp_injective he)
  have hXE : X-E≠0 := by
    intro h
    have he : -θ*(u:ℝ)= -θ := Real.exp_injective (sub_eq_zero.mp h)
    exact hu1 ((mul_left_cancel₀ (neg_ne_zero.mpr hθ)) (by simpa using he))
  let D : ℝ → ℝ := fun v => (X-E)+(1-X)*Real.exp (-θ*v)
  have hD (v : ℝ) : D v=frankDen θ u v := by dsimp [D,X,E,frankDen]; ring
  have hd (v : ℝ) (hv : v∈Icc 0 1) : D v≠0 := by
    rw [hD]
    exact frankDen_ne_zero hθ u (⟨v,hv⟩:I)
  let F : ℝ → ℝ := fun v => X/(θ*(X-E))*(θ*v+(1-E)/(1-X)*Real.log (D v))
  let f : ℝ → ℝ := fun v => X*(1-Real.exp (-θ*v))/D v
  have hF (v : ℝ) (hv : v∈uIcc 0 1) : HasDerivAt F (f v) v :=
    frank_partial_primitive θ E X v hθ hX hXE (hd v (by simpa using hv))
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by dsimp [D]; fun_prop)
    intro v hv
    exact hd v (by simpa using hv)
  have he : (fun v : I => frankPartial θ u v)=fun v : I => f (v:ℝ) := by
    funext v
    dsimp only [frankPartial,f,X]
    rw [hD]
  rw [he,Copula.integral_unitInterval f,intervalIntegral.integral_eq_sub_of_hasDerivAt hF hi]
  have hD0 : D 0=1-E := by dsimp [D]; simp
  have hD1 : D 1=X*(1-E) := by dsimp [D,E]; simp only [mul_one]; ring
  dsimp only [F]
  rw [hD0,hD1,Real.log_mul hX0 hE]
  have hl : Real.log X= -θ*(u:ℝ) := Real.log_exp _
  rw [hl]
  change X/(θ*(X-E))*(θ*1+(1-E)/(1-X)*(-θ*(u:ℝ)+Real.log (1-E)))-
    X/(θ*(X-E))*(θ*0+(1-E)/(1-X)*Real.log (1-E))=
      X/(X-E)*(1-(u:ℝ)*(1-E)/(1-X))
  field_simp
  ring

theorem integral_frankPartial_second_debye {θ : ℝ} (hθ : θ≠0) (u : I)
    (hu0 : (u:ℝ)≠0) (hu1 : (u:ℝ)≠1) :
    (∫ v : I, frankPartial θ u v)=
      (1-(u:ℝ))+(1-(u:ℝ))/(Real.exp (θ*(1-(u:ℝ)))-1)-
        (u:ℝ)/(Real.exp (θ*(u:ℝ))-1) := by
  rw [integral_frankPartial_second hθ u hu0 hu1]
  let E := Real.exp (-θ)
  let X := Real.exp (-θ*(u:ℝ))
  have hX0 : X≠0 := Real.exp_ne_zero _
  have hE0 : E≠0 := Real.exp_ne_zero _
  have hX : 1-X≠0 := by
    intro h
    have he : Real.exp (-θ*(u:ℝ))=Real.exp 0 := by simpa [X] using (sub_eq_zero.mp h).symm
    exact (mul_ne_zero (neg_ne_zero.mpr hθ) hu0) (Real.exp_injective he)
  have hXE : X-E≠0 := by
    intro h
    have he : -θ*(u:ℝ)= -θ := Real.exp_injective (sub_eq_zero.mp h)
    exact hu1 ((mul_left_cancel₀ (neg_ne_zero.mpr hθ)) (by simpa using he))
  have he1 : Real.exp (θ*(1-(u:ℝ)))=X/E := by
    dsimp [X,E]
    rw [← Real.exp_sub]
    congr 1
    ring
  have he2 : Real.exp (θ*(u:ℝ))=X⁻¹ := by
    dsimp [X]
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [he1,he2]
  change X/(X-E)*(1-(u:ℝ)*(1-E)/(1-X))=
    (1-(u:ℝ))+(1-(u:ℝ))/(X/E-1)-(u:ℝ)/(X⁻¹-1)
  field_simp [hX0,hE0,hX,hXE]
  ring

theorem frank_rho_conditional_integral (C : Copula 2) {θ : ℝ} (hθ : θ≠0)
    (hc : ∀ u v : I, C.cdf ![u,v]=frankRealCDF θ u v) :
    C.spearmanRho=12*(∫ u : I, (1-(u:ℝ))*(∫ v : I, frankPartial θ u v))-3 := by
  rw [rho_conditional_formula]
  have he : (∫ v : I, ∫ u : I, (1-(u:ℝ))*C.conditionalCDF u v)=
      ∫ v : I, ∫ u : I, (1-(u:ℝ))*frankPartial θ u v := by
    apply integral_congr_ae
    filter_upwards [] with v
    apply integral_congr_ae
    filter_upwards [frank_conditionalCDF_of_cdf C hθ hc v] with u hu
    rw [hu]
  rw [he]
  have hi : Integrable (fun p : I × I => (1-(p.2:ℝ))*frankPartial θ p.2 p.1)
      ((volume : Measure I).prod volume) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply Continuous.mul (by fun_prop)
    unfold frankPartial
    apply Continuous.div (by fun_prop) (by unfold frankDen; fun_prop)
    intro p
    exact frankDen_ne_zero hθ p.2 p.1
  rw [integral_integral_swap hi]
  simp_rw [integral_const_mul]

theorem frank_spearmanRho_of_cdf (C : Copula 2) {θ : ℝ} (hθ : θ≠0)
    (hc : ∀ u v : I, C.cdf ![u,v]=frankRealCDF θ u v) :
    C.spearmanRho=1-12/θ*(debyeOne θ-debyeTwo θ) := by
  rw [frank_rho_conditional_integral C hθ hc]
  let q : I → ℝ := fun u => (u:ℝ)/(Real.exp (θ*(u:ℝ))-1)
  let r : I → ℝ := fun u => (u:ℝ)^2/(Real.exp (θ*(u:ℝ))-1)
  have hq : Integrable q := integrable_debye_section hθ
  have hr : Integrable r := integrable_debye_second_section hθ
  have hs : Integrable (fun u : I => r (unitInterval.symm u)) :=
    unitInterval.measurePreserving_symm.integrable_comp_of_integrable hr
  have hp : Integrable (fun u : I => (1-(u:ℝ))^2) :=
    Copula.integrable_continuous_unit volume (by fun_prop)
  have he : (∫ u : I, (1-(u:ℝ))*(∫ v : I, frankPartial θ u v))=
      ∫ u : I, (1-(u:ℝ))^2+r (unitInterval.symm u)-(q u-r u) := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure I) 0,Measure.ae_ne (volume : Measure I) 1] with u hu0 hu1
    rw [integral_frankPartial_second_debye hθ u (fun h => hu0 (Subtype.ext h)) (fun h => hu1 (Subtype.ext h))]
    dsimp only [q,r]
    rw [unitInterval.coe_symm_eq]
    ring
  have hsum : Integrable (fun u : I => (1-(u:ℝ))^2+r (unitInterval.symm u)) := hp.add hs
  have hdiff : Integrable (fun u : I => q u-r u) := hq.sub hr
  have hdiffeq : (∫ u : I, q u-r u)=(∫ u : I, q u)-(∫ u : I, r u) := integral_sub hq hr
  rw [he,integral_sub hsum hdiff,integral_add hp hs,hdiffeq,integral_unit_reflection r]
  have hpoly : (∫ u : I, (1-(u:ℝ))^2)=(1:ℝ)/3 := by
    have he' : (fun u : I => (1-(u:ℝ))^2)=fun u : I => ((unitInterval.symm u: I):ℝ)^2 := by
      funext u; rw [unitInterval.coe_symm_eq]
    rw [he',integral_unit_reflection (fun u : I => (u:ℝ)^2),Copula.integral_unit_pow]
    norm_num
  rw [hpoly]
  change 12*((1/3+∫ u : I, (u:ℝ)^2/(Real.exp (θ*(u:ℝ))-1))-
    ((∫ u : I, (u:ℝ)/(Real.exp (θ*(u:ℝ))-1))-
      ∫ u : I, (u:ℝ)^2/(Real.exp (θ*(u:ℝ))-1)))-3=_
  rw [integral_debye_section hθ,integral_debye_second_section hθ]
  ring

end Verification
