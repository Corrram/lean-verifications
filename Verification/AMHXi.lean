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

theorem amh_conditionalCDF {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (v : I) :
    (fun u => (amh θ hmin hmax.le).conditionalCDF u v) =ᵐ[volume]
      fun u => amhPartial θ u v := by
  filter_upwards [(amh θ hmin hmax.le).conditionalCDF_eq_deriv v,
    Measure.ae_ne volume (0:I),Measure.ae_ne volume (1:I)] with u hu hu0 hu1
  rw [hu]
  have h0 : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu0 (Subtype.ext h)))
  have h1 : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))
  have he : cdfSection (amh θ hmin hmax.le) v =ᶠ[𝓝 (u:ℝ)]
      fun x => x*(v:ℝ)/amhDen θ x v := by
    filter_upwards [Ioo_mem_nhds h0 h1] with x hx
    have hh := cdf_amh θ hmin hmax.le (⟨x,hx.1.le,hx.2.le⟩:I) v
    simpa only [cdfSection,projIcc_of_mem zero_le_one ⟨hx.1.le,hx.2.le⟩,amhDen] using hh
  exact ((amh_cdf_derivative (amhDen_pos_lt_one hmax u.property v.property).ne').congr_of_eventuallyEq he).deriv

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

theorem integral_amhPartial_sq {θ : ℝ} (hθ : θ<1) (v : I) :
    (∫ u : I, (amhPartial θ u v)^2)=
      (v:ℝ)^2*((1-θ*(1-(v:ℝ)))^2+(1-θ*(1-(v:ℝ)))+1)/(3*(1-θ*(1-(v:ℝ)))) := by
  let A := 1-θ*(1-(v:ℝ))
  let B := θ*(1-(v:ℝ))
  have hA : 0<A := by
    simpa only [amhDen,sub_zero,mul_one] using amhDen_pos_lt_one hθ (show (0:ℝ)∈Icc 0 1 by norm_num) v.property
  have hAB : A+B=1 := by dsimp [A,B]; ring
  have hd (u : ℝ) (hu : u∈Icc 0 1) : 0<A+B*u := by
    have hh := amhDen_pos_lt_one hθ hu v.property
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

end Verification
