import Verification.AMHXi
import Verification.KendallConditionalProduct

/-! # Kendall tau for Ali–Mikhail–Haq copulas -/

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

private theorem amh_product_primitive (A B c θ v x : ℝ) (hA : A≠0) (hd : A+B*x≠0) :
    HasDerivAt (fun u : ℝ => v*u^2*(c*(3*A+B*u)+2*A*θ*u)/(6*A*(A+B*u)^3))
      (x*v*A*(c+θ*x)/(A+B*x)^4) x := by
  have hn := (((hasDerivAt_id x).pow 2).const_mul v).mul
    (((((hasDerivAt_id x).const_mul B).const_add (3*A)).const_mul c).add
      ((hasDerivAt_id x).const_mul (2*A*θ)))
  have hd' := ((((hasDerivAt_id x).const_mul B).const_add A).pow 3).const_mul (6*A)
  convert hn.div hd' (mul_ne_zero (mul_ne_zero (by norm_num) hA) (pow_ne_zero 3 hd)) using 1
  · funext u; rfl
  · dsimp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply,id_eq]
    field_simp [hA, hd]
    have hd'' : A+x*B≠0 := by simpa [mul_comm] using hd
    field_simp [hd'']
    ring

theorem integral_amhPartial_product_of_den_pos {θ : ℝ} (v : I)
    (hden : ∀ u : ℝ, u∈Icc 0 1 → 0<amhDen θ u v) :
    (∫ u : I, amhPartial θ u v*amhPartial θ v u)=
      (v:ℝ)/3+(1-θ)*(v:ℝ)/(6*(1-θ*(1-(v:ℝ)))) := by
  let A := 1-θ*(1-(v:ℝ))
  let B := θ*(1-(v:ℝ))
  have hA : 0<A := by
    simpa only [amhDen,sub_zero,mul_one] using
      hden 0 (by norm_num)
  have hd (u : ℝ) (hu : u∈Icc 0 1) : 0<A+B*u := by
    have hh := hden u hu
    convert hh using 1
    dsimp [A,B,amhDen]
    ring
  let F : ℝ → ℝ := fun u => (v:ℝ)*u^2*((1-θ)*(3*A+B*u)+2*A*θ*u)/(6*A*(A+B*u)^3)
  let f : ℝ → ℝ := fun u => u*(v:ℝ)*A*((1-θ)+θ*u)/(A+B*u)^4
  have hF (u : ℝ) (hu : u∈uIcc 0 1) : HasDerivAt F (f u) u :=
    amh_product_primitive A B (1-θ) θ v u hA.ne' (hd u (by simpa using hu)).ne'
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    exact pow_ne_zero 4 (hd u (by simpa using hu)).ne'
  have he : (fun u : I => amhPartial θ u v*amhPartial θ v u)=fun u : I => f (u:ℝ) := by
    funext u
    have hd' := (hden u u.property).ne'
    have hs : amhDen θ (v:ℝ) u=amhDen θ u v := by unfold amhDen; ring
    have hd'' : A+B*(u:ℝ)=amhDen θ u v := by dsimp [A,B,amhDen]; ring
    dsimp only [amhPartial,f]
    rw [hs,hd'']
    field_simp [hd']
    dsimp [A]
    ring
  rw [he,Copula.integral_unitInterval f,intervalIntegral.integral_eq_sub_of_hasDerivAt hF hi]
  have hAB : A+B=1 := by dsimp [A,B]; ring
  simp only [F,one_pow,mul_one,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_mul,
    zero_div,sub_zero,hAB]
  change (v:ℝ)*((1-θ)*(3*A+B)+2*A*θ)/(6*A)=(v:ℝ)/3+(1-θ)*(v:ℝ)/(6*A)
  rw [show B=1-A by linarith]
  field_simp
  ring

theorem integral_amhPartial_product {θ : ℝ} (hθ : θ<1) (v : I) :
    (∫ u : I, amhPartial θ u v*amhPartial θ v u)=
      (v:ℝ)/3+(1-θ)*(v:ℝ)/(6*(1-θ*(1-(v:ℝ)))) :=
  integral_amhPartial_product_of_den_pos v (fun _ hu => amhDen_pos_lt_one hθ hu v.property)

theorem amh_kendallTau_integral {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) :
    (amh θ hmin hmax.le).kendallTau=
      1-4*(∫ v : I, (v:ℝ)/3+(1-θ)*(v:ℝ)/(6*(1-θ*(1-(v:ℝ))))) := by
  let C := amh θ hmin hmax.le
  have hCt : C.transpose=C := by
    apply Copula.ext_cdf
    intro z
    have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
    rw [hz,Copula.cdf_transpose]
    simp only [C,cdf_amh]
    ring
  have ha : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF v u=amhPartial θ v u := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u=amhPartial θ v u)
      (measurableSet_eq_fun C.measurable_conditionalCDF (by unfold amhPartial amhDen; fun_prop))).mp
    exact Eventually.of_forall (amh_conditionalCDF hmin hmax)
  change C.kendallTau=_
  rw [kendallTau_conditional_product,hCt]
  congr 2
  apply integral_congr_ae
  filter_upwards [ha] with v hv
  have he : (fun u : I => C.conditionalCDF v u*C.conditionalCDF u v) =ᵐ[volume]
      fun u => amhPartial θ u v*amhPartial θ v u := by
    filter_upwards [hv,amh_conditionalCDF hmin hmax v] with u hu hv'
    rw [hu,hv',mul_comm]
  rw [integral_congr_ae he]
  exact integral_amhPartial_product hmax v

private noncomputable def amhTauPrimitive (θ v : ℝ) : ℝ :=
  v^2/6+(1-θ)*v/(6*θ)-(1-θ)^2/(6*θ^2)*Real.log (1-θ+θ*v)

private theorem amhTauPrimitive_deriv (θ v : ℝ) (hθ : θ≠0) (hd : 1-θ+θ*v≠0) :
    HasDerivAt (amhTauPrimitive θ) (v/3+(1-θ)*v/(6*(1-θ*(1-v)))) v := by
  have hl := (((hasDerivAt_id v).const_mul θ).const_add (1-θ)).log hd
  have hh := (((((hasDerivAt_id v).pow 2).div_const 6).add
    (((hasDerivAt_id v).const_mul (1-θ)).div_const (6*θ))).sub
    (hl.const_mul ((1-θ)^2/(6*θ^2))))
  convert hh using 1
  · funext u; rfl
  · have hd' : 1+v*θ-θ≠0 := by convert hd using 1; ring
    dsimp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.pow_apply,id_eq]
    field_simp [hθ,hd']
    ring_nf
    field_simp [hd']
    ring

theorem amh_kendallTau {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    (amh θ hmin hmax.le).kendallTau=
      1-2/(3*θ)-2*(1-θ)^2*Real.log (1-θ)/(3*θ^2) := by
  rw [amh_kendallTau_integral hmin hmax]
  let f : ℝ → ℝ := fun v => v/3+(1-θ)*v/(6*(1-θ*(1-v)))
  have hd (v : ℝ) (hv : v∈Icc 0 1) : 0<1-θ*(1-v) := by
    simpa only [amhDen,sub_zero,mul_one] using
      amhDen_pos_lt_one hmax (show (0:ℝ)∈Icc 0 1 by norm_num) hv
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro v hv
    exact mul_ne_zero (by norm_num) (hd v (by simpa using hv)).ne'
  have hF (v : ℝ) (hv : v∈uIcc (0:ℝ) 1) : HasDerivAt (amhTauPrimitive θ) (f v) v := by
    apply amhTauPrimitive_deriv θ v h0
    have hh := hd v (by simpa using hv)
    nlinarith
  change 1-4*(∫ v : I, f (v:ℝ))=_
  rw [Copula.integral_unitInterval f,intervalIntegral.integral_eq_sub_of_hasDerivAt hF hi]
  unfold amhTauPrimitive
  simp only [one_pow,mul_one,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,
    zero_div,add_zero]
  rw [show 1-θ+θ=1 by ring,Real.log_one]
  field_simp
  ring

theorem amh_kendallTau_zero : (amh 0 (by norm_num) (by norm_num)).kendallTau=0 := by
  rw [amh_zero]
  simp

theorem amh_kendallTau_one : (amh 1 (by norm_num) le_rfl).kendallTau=1/3 := by
  let C := amh 1 (by norm_num) le_rfl
  have hCt : C.transpose=C := by
    apply Copula.ext_cdf
    intro z
    have hz : z=![z 0,z 1] := by funext i; fin_cases i <;> rfl
    rw [hz,Copula.cdf_transpose]
    simp only [C,cdf_amh]
    ring
  have hd (v : I) (hv : 0<(v:ℝ)) (u : ℝ) (hu : u∈Icc 0 1) : 0<amhDen 1 u v := by
    have hh := mul_nonneg hu.1 (sub_nonneg.mpr v.property.2)
    unfold amhDen
    nlinarith
  have ha : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v=amhPartial 1 u v := by
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
    exact amh_conditionalCDF_of_den_pos (by norm_num) le_rfl v (fun u => hd v hvp u u.property)
  have hb : ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF v u=amhPartial 1 v u := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun u v => C.conditionalCDF v u=amhPartial 1 v u)
      (measurableSet_eq_fun C.measurable_conditionalCDF (by unfold amhPartial amhDen; fun_prop))).mp
    exact ha
  change C.kendallTau=_
  rw [kendallTau_conditional_product,hCt]
  have he : (∫ v : I, ∫ u : I, C.conditionalCDF v u*C.conditionalCDF u v)=
      ∫ v : I, (v:ℝ)/3 := by
    apply integral_congr_ae
    filter_upwards [ha,hb,Measure.ae_ne (volume : Measure I) 0] with v hv hv' hv0
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv0 (Subtype.ext h)))
    have he' : (fun u : I => C.conditionalCDF v u*C.conditionalCDF u v) =ᵐ[volume]
        fun u => amhPartial 1 u v*amhPartial 1 v u := by
      filter_upwards [hv,hv'] with u hu hu'
      rw [hu,hu',mul_comm]
    rw [integral_congr_ae he',integral_amhPartial_product_of_den_pos v (hd v hvp)]
    norm_num
  rw [he,integral_div,Copula.integral_unit_id]
  norm_num

end Verification
