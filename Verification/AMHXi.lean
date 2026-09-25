import Verification.AMHDensity
import Copula.Rank.ConditionalDerivative
import Copula.Rank.ConditionalCDF

/-! # Chatterjee xi for Ali–Mikhail–Haq copulas -/

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem amhDen_pos_lt_one {θ u v : ℝ} (hθ : θ<1)
    (hu : u∈Icc 0 1) (hv : v∈Icc 0 1) : 0<amhDen θ u v := by
  by_cases h0 : 0≤θ
  · exact amhDen_pos h0 hθ hu hv
  · have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h0)
      (mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hv.2))
    unfold amhDen
    nlinarith

theorem amh_conditionalCDF_of_den_pos {θ : ℝ} (hmin : -1≤θ) (hmax : θ≤1) (v : I)
    (hd : ∀ u : I, 0<amhDen θ u v) :
    (fun u => (amh θ hmin hmax).conditionalCDF u v) =ᵐ[volume]
      fun u => amhPartial θ u v := by
  filter_upwards [(amh θ hmin hmax).conditionalCDF_eq_deriv v,
    Measure.ae_ne volume (0:I),Measure.ae_ne volume (1:I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  have he : cdfSection (amh θ hmin hmax) v =ᶠ[𝓝 (u:ℝ)]
      fun x => x*(v:ℝ)/amhDen θ x v := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    have hh := cdf_amh θ hmin hmax (⟨x,hx.1.le,hx.2.le⟩:I) v
    simpa only [cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩,amhDen] using hh
  exact ((amh_cdf_derivative (hd u).ne').congr_of_eventuallyEq he).deriv

theorem amh_conditionalCDF {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (v : I) :
    (fun u => (amh θ hmin hmax.le).conditionalCDF u v) =ᵐ[volume]
      fun u => amhPartial θ u v :=
  amh_conditionalCDF_of_den_pos hmin hmax.le v
    (fun u => amhDen_pos_lt_one hmax u.property v.property)

private theorem rational_fourth_primitive (A B v x : ℝ) (hA : A≠0) (hd : A+B*x≠0) :
    HasDerivAt (fun u : ℝ => v^2*u*(3*A^2+3*A*B*u+B^2*u^2)/(3*A*(A+B*u)^3))
      ((v*A/(A+B*x)^2)^2) x := by
  have hnum := (((hasDerivAt_id x).const_mul (v^2)).mul
    (((hasDerivAt_const x (3*A^2)).add ((hasDerivAt_id x).const_mul (3*A*B))).add
      (((hasDerivAt_id x).pow 2).const_mul (B^2))))
  have hden := ((((hasDerivAt_id x).const_mul B).const_add A).pow 3).const_mul (3*A)
  convert hnum.div hden (mul_ne_zero (mul_ne_zero (by norm_num) hA) (pow_ne_zero 3 hd)) using 1
  · funext u; rfl
  · dsimp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply,id_eq]
    field_simp
    ring

theorem integral_amhPartial_sq_of_den_pos {θ : ℝ} (v : I)
    (hden : ∀ u : ℝ, u∈Icc 0 1 → 0<amhDen θ u v) :
    (∫ u : I, (amhPartial θ u v)^2)=
      (v:ℝ)^2*((1-θ*(1-(v:ℝ)))^2+(1-θ*(1-(v:ℝ)))+1)/(3*(1-θ*(1-(v:ℝ)))) := by
  let A := 1-θ*(1-(v:ℝ))
  let B := θ*(1-(v:ℝ))
  have hA : 0<A := by
    simpa only [amhDen,sub_zero,mul_one] using hden 0 (by norm_num)
  have hAB : A+B=1 := by dsimp [A,B]; ring
  have hd (u : ℝ) (hu : u∈Icc 0 1) : 0<A+B*u := by
    have hh := hden u hu
    convert hh using 1
    dsimp [A,B,amhDen]
    ring
  let F : ℝ → ℝ := fun u => (v:ℝ)^2*u*(3*A^2+3*A*B*u+B^2*u^2)/(3*A*(A+B*u)^3)
  let f : ℝ → ℝ := fun u => ((v:ℝ)*A/(A+B*u)^2)^2
  have hF (u : ℝ) (hu : u∈Icc 0 1) : HasDerivAt F (f u) u :=
    rational_fourth_primitive A B v u hA.ne' (hd u hu).ne'
  have hf : ContinuousOn f (Icc 0 1) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro u hu
    exact pow_ne_zero 2 (hd u hu).ne'
  have hfun : (fun u : I => (amhPartial θ u v)^2)=fun u : I => f (u:ℝ) := by
    funext u
    dsimp [f,amhPartial,amhDen,A,B]
    congr 2
    ring
  rw [hfun,Copula.integral_unitInterval f]
  have hi : IntervalIntegrable f volume 0 1 :=
    (show ContinuousOn f (uIcc 0 1) by simpa using hf).intervalIntegrable
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hF u (by simpa using hu)) hi
  rw [hh]
  simp only [F,mul_one,one_pow,mul_zero,zero_mul,zero_pow (by norm_num : (2:ℕ)≠0),
    zero_div,sub_zero,hAB]
  change (v:ℝ)^2*(3*A^2+3*A*B+B^2)/(3*A)=(v:ℝ)^2*(A^2+A+1)/(3*A)
  rw [show B=1-A by linarith]
  ring

theorem integral_amhPartial_sq {θ : ℝ} (hθ : θ<1) (v : I) :
    (∫ u : I, (amhPartial θ u v)^2)=
      (v:ℝ)^2*((1-θ*(1-(v:ℝ)))^2+(1-θ*(1-(v:ℝ)))+1)/(3*(1-θ*(1-(v:ℝ)))) :=
  integral_amhPartial_sq_of_den_pos v (fun _ hu => amhDen_pos_lt_one hθ hu v.property)

theorem amh_xi_integral {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) :
    (amh θ hmin hmax.le).chatterjeeXi=
      6*(∫ v : I, (v:ℝ)^2*((1-θ*(1-(v:ℝ)))^2+(1-θ*(1-(v:ℝ)))+1)/(3*(1-θ*(1-(v:ℝ)))))-2 := by
  unfold chatterjeeXi
  congr 2
  apply integral_congr_ae
  exact Eventually.of_forall fun v =>
    (integral_congr_ae ((amh_conditionalCDF hmin hmax v).fun_comp (fun x => x^2))).trans
      (integral_amhPartial_sq hmax v)

private noncomputable def amhXiPrimitive (θ v : ℝ) : ℝ :=
  (2-θ)*v^3/9+θ*v^4/12+v^2/(6*θ)-(1-θ)*v/(3*θ^2)+
    (1-θ)^2/(3*θ^3)*Real.log (1-θ+θ*v)

private theorem amhXiPrimitive_deriv (θ v : ℝ) (hθ : θ≠0) (hd : 1-θ+θ*v≠0) :
    HasDerivAt (amhXiPrimitive θ)
      (v^2*((1-θ*(1-v))^2+(1-θ*(1-v))+1)/(3*(1-θ*(1-v)))) v := by
  have hl := (((hasDerivAt_id v).const_mul θ).const_add (1-θ)).log hd
  have hh := (((((((hasDerivAt_id v).pow 3).const_mul (2-θ)).div_const 9).add
    ((((hasDerivAt_id v).pow 4).const_mul θ).div_const 12)).add
    (((hasDerivAt_id v).pow 2).div_const (6*θ))).sub
    (((hasDerivAt_id v).const_mul (1-θ)).div_const (3*θ^2))).add
    (hl.const_mul ((1-θ)^2/(3*θ^3)))
  convert hh using 1
  · funext u; rfl
  · have hd' : 1-θ*(1-v)≠0 := by convert hd using 1; ring
    have hd'' : 1+v*θ-θ≠0 := by convert hd using 1; ring
    dsimp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.div_apply,Pi.pow_apply,id_eq]
    field_simp [hd'']
    ring_nf
    field_simp [hd'']
    ring

theorem amh_chatterjeeXi {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    (amh θ hmin hmax.le).chatterjeeXi=
      -θ/6-2/3+3/θ-2/θ^2-2*(θ-1)^2*Real.log (1-θ)/θ^3 := by
  rw [amh_xi_integral hmin hmax]
  let f : ℝ → ℝ := fun v => v^2*((1-θ*(1-v))^2+(1-θ*(1-v))+1)/(3*(1-θ*(1-v)))
  have hd (v : ℝ) (hv : v∈Icc 0 1) : 0<1-θ*(1-v) := by
    simpa only [amhDen,sub_zero,mul_one] using
      amhDen_pos_lt_one hmax (show (0:ℝ)∈Icc 0 1 by norm_num) hv
  have hi : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro v hv
    have hv' : v∈Icc (0:ℝ) 1 := by simpa using hv
    exact mul_ne_zero (by norm_num) (hd v hv').ne'
  have hF (v : ℝ) (hv : v∈uIcc (0:ℝ) 1) : HasDerivAt (amhXiPrimitive θ) (f v) v := by
    apply amhXiPrimitive_deriv θ v h0
    have hh := hd v (by simpa using hv)
    nlinarith
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hF hi
  change 6*(∫ v : I, f (v:ℝ))-2=_
  rw [Copula.integral_unitInterval f,hh]
  unfold amhXiPrimitive
  simp only [one_pow,mul_one,sub_self,add_zero,zero_pow (by norm_num : (3:ℕ)≠0),
    zero_pow (by norm_num : (4:ℕ)≠0),zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,
    zero_div,zero_add]
  rw [show 1-θ+θ=1 by ring,Real.log_one]
  field_simp
  ring

theorem amh_chatterjeeXi_zero : (amh 0 (by norm_num) (by norm_num)).chatterjeeXi=0 := by
  rw [amh_zero]
  simp

theorem amh_chatterjeeXi_one : (amh 1 (by norm_num) le_rfl).chatterjeeXi=1/6 := by
  let C := amh 1 (by norm_num) le_rfl
  have hd (v : I) (hv : 0<(v:ℝ)) (u : ℝ) (hu : u∈Icc 0 1) : 0<amhDen 1 u v := by
    have hh := mul_nonneg hu.1 (sub_nonneg.mpr v.property.2)
    unfold amhDen
    nlinarith
  have he : (∫ v : I, ∫ u : I, (C.conditionalCDF u v)^2)=
      ∫ v : I, ((v:ℝ)^3+(v:ℝ)^2+(v:ℝ))/3 := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure I) 0] with v hv
    have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
    have hcond := amh_conditionalCDF_of_den_pos (θ:=1) (by norm_num) le_rfl v (fun u => hd v hvp u u.property)
    have hsquare : (fun u : I => (C.conditionalCDF u v)^2) =ᵐ[volume]
        fun u => (amhPartial 1 u v)^2 := hcond.fun_comp (fun x => x^2)
    rw [integral_congr_ae hsquare,integral_amhPartial_sq_of_den_pos v (hd v hvp)]
    simp only [one_mul,sub_sub_cancel]
    field_simp
  change 6*(∫ v : I, ∫ u : I, (C.conditionalCDF u v)^2)-2=1/6
  rw [he,integral_div]
  have h1 : Integrable (fun v : I => (v:ℝ)) := Copula.integrable_continuous_unit volume continuous_subtype_val
  have h2 : Integrable (fun v : I => (v:ℝ)^2) := Copula.integrable_continuous_unit volume (by fun_prop)
  have h3 : Integrable (fun v : I => (v:ℝ)^3) := Copula.integrable_continuous_unit volume (by fun_prop)
  have h32 : Integrable (fun v : I => (v:ℝ)^3+(v:ℝ)^2) := h3.add h2
  rw [integral_add h32 h1,integral_add h3 h2,Copula.integral_unit_pow,Copula.integral_unit_pow,Copula.integral_unit_id]
  norm_num

theorem amh_xi_regular_integral {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) :
    (amh θ hmin hmax.le).chatterjeeXi=
      2*θ^2*∫ v : I, (v:ℝ)^2*(1-(v:ℝ))^2/(1-θ*(1-(v:ℝ))) := by
  have hd (v : I) : 0<1-θ*(1-(v:ℝ)) := by
    simpa only [amhDen,sub_zero,mul_one] using
      amhDen_pos_lt_one hmax (show (0:ℝ)∈Icc 0 1 by norm_num) v.property
  have hi : Integrable (fun v : I => (v:ℝ)^2*(1-(v:ℝ))^2/(1-θ*(1-(v:ℝ)))) :=
    Copula.integrable_continuous_unit volume (Continuous.div (by fun_prop) (by fun_prop) (fun v => (hd v).ne'))
  have hi2 : Integrable (fun v : I => (v:ℝ)^2) := Copula.integrable_continuous_unit volume (by fun_prop)
  have he (v : I) : (v:ℝ)^2*((1-θ*(1-(v:ℝ)))^2+(1-θ*(1-(v:ℝ)))+1)/(3*(1-θ*(1-(v:ℝ))))=
      (v:ℝ)^2+(θ^2/3)*((v:ℝ)^2*(1-(v:ℝ))^2/(1-θ*(1-(v:ℝ)))) := by
    field_simp [(hd v).ne']
    ring
  rw [amh_xi_integral hmin hmax]
  simp_rw [he]
  rw [integral_add hi2 (hi.const_mul _),integral_const_mul,Copula.integral_unit_pow]
  ring

theorem amh_xi_bound_near_zero {θ : ℝ} (hmin : -1≤θ) (hhalf : θ≤1/2) :
    (amh θ hmin (by linarith)).chatterjeeXi≤4*θ^2 := by
  have hmax : θ<1 := by linarith
  have hd (v : I) : 1/2≤1-θ*(1-(v:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hhalf (sub_nonneg.mpr v.property.2)
    linarith [v.property.1]
  have hi : Integrable (fun v : I => (v:ℝ)^2*(1-(v:ℝ))^2/(1-θ*(1-(v:ℝ)))) :=
    Copula.integrable_continuous_unit volume (Continuous.div (by fun_prop) (by fun_prop) (fun v => by have := hd v; linarith))
  have hq (v : I) : (v:ℝ)^2*(1-(v:ℝ))^2/(1-θ*(1-(v:ℝ)))≤2 := by
    apply (div_le_iff₀ (by have := hd v; linarith)).mpr
    have h1 : (v:ℝ)^2≤1 := by nlinarith [v.property.1,v.property.2]
    have h2 : (1-(v:ℝ))^2≤1 := by nlinarith [v.property.1,v.property.2]
    have hh := mul_le_mul_of_nonneg_right h1 (sq_nonneg (1-(v:ℝ)))
    nlinarith [hd v]
  have hh := integral_mono hi (integrable_const (2:ℝ)) hq
  simp only [integral_const,Measure.real_def,measure_univ,ENNReal.toReal_one,one_smul] at hh
  rw [amh_xi_regular_integral hmin hmax]
  nlinarith [sq_nonneg θ,mul_le_mul_of_nonneg_left hh (show 0≤2*θ^2 by positivity)]

theorem amh_xi_tendsto_zero {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hmin : ∀ x, -1≤θ x) (hmax : ∀ x, θ x≤1) (hθ : Tendsto θ l (𝓝 0)) :
    Tendsto (fun x => (amh (θ x) (hmin x) (hmax x)).chatterjeeXi) l (𝓝 0) := by
  have hh : ∀ᶠ x in l, θ x<1/2 := (tendsto_order.1 hθ).2 (1/2) (by norm_num)
  have hb : Tendsto (fun x => 4*(θ x)^2) l (𝓝 0) := by
    simpa using (hθ.pow 2).const_mul 4
  apply squeeze_zero' (Eventually.of_forall fun x => (amh (θ x) (hmin x) (hmax x)).chatterjeeXi_nonneg) _ hb
  filter_upwards [hh] with x hx
  exact amh_xi_bound_near_zero (hmin x) hx.le

end Verification
