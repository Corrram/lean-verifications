import Copula.Classical
import Copula.Classical.Bivariate
import Copula.Dependence.Density
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

/-- CDF of a power distribution supported on [0,t]. Its value at t=0 is irrelevant to integration. -/
noncomputable def rafteryKernel (a : ℝ) (u t : I) : ℝ :=
  if t ≤ u then 1 else ((u:ℝ)/(t:ℝ))^a

theorem rafteryKernel_nonneg (a : ℝ) (u t : I) : 0 ≤ rafteryKernel a u t := by
  unfold rafteryKernel
  split_ifs
  · norm_num
  · exact Real.rpow_nonneg (div_nonneg u.property.1 t.property.1) _

theorem rafteryKernel_le_one {a : ℝ} (ha : 0 ≤ a) (u t : I) :
    rafteryKernel a u t ≤ 1 := by
  unfold rafteryKernel
  split_ifs with h
  · exact le_rfl
  · have ht : 0 < (t:ℝ) := lt_of_le_of_lt u.property.1 (lt_of_not_ge h)
    exact Real.rpow_le_one (div_nonneg u.property.1 t.property.1)
      ((div_le_one ht).mpr (le_of_lt (lt_of_not_ge h))) ha

theorem rafteryKernel_monotone {a : ℝ} (ha : 0 ≤ a) (t : I) :
    Monotone (fun u => rafteryKernel a u t) := by
  intro u v huv
  change rafteryKernel a u t ≤ rafteryKernel a v t
  by_cases hv : t ≤ v
  · have he : rafteryKernel a v t = 1 := by simp [rafteryKernel,hv]
    rw [he]
    exact rafteryKernel_le_one ha u t
  have hu : ¬t ≤ u := fun h => hv (h.trans huv)
  simp only [rafteryKernel,hu,hv,ite_false]
  exact Real.rpow_le_rpow (div_nonneg u.property.1 t.property.1)
    (div_le_div_of_nonneg_right huv t.property.1) ha

theorem rafteryKernel_measurable (a : ℝ) (u : I) : Measurable (rafteryKernel a u) := by
  unfold rafteryKernel
  exact Measurable.ite measurableSet_Iic measurable_const (by fun_prop)

theorem rafteryKernel_integrable {a : ℝ} (ha : 0 ≤ a) (u : I) :
    Integrable (rafteryKernel a u) := by
  refine (integrable_const (1:ℝ)).mono' (rafteryKernel_measurable a u).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rafteryKernel_nonneg a u t)]
    exact rafteryKernel_le_one ha u t

theorem rafteryKernel_product_integrable {a : ℝ} (ha : 0 ≤ a) (u v : I) :
    Integrable (fun t => rafteryKernel a u t * rafteryKernel a v t) := by
  refine (integrable_const (1:ℝ)).mono'
    ((rafteryKernel_measurable a u).mul (rafteryKernel_measurable a v)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rafteryKernel_nonneg a u t)
      (rafteryKernel_nonneg a v t))]
    calc
      _ ≤ 1 * rafteryKernel a v t := mul_le_mul_of_nonneg_right
        (rafteryKernel_le_one ha u t) (rafteryKernel_nonneg a v t)
      _ ≤ 1 := by simpa only [one_mul] using rafteryKernel_le_one ha v t

private theorem integral_unit_Ioi_real (f : ℝ → ℝ) (u : I) :
    (∫ t in Ioi u, f (t:ℝ)) = ∫ t in (u:ℝ)..1, f t := by
  rw [← integral_indicator measurableSet_Ioi]
  change (∫ t : I, (Ioi (u:ℝ)).indicator f (t:ℝ)) = _
  rw [Copula.integral_unitInterval, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_indicator measurableSet_Ioi, intervalIntegral.integral_of_le u.property.2]
  have hs : Ioc (0:ℝ) 1 ∩ Ioi (u:ℝ) = Ioc (u:ℝ) 1 := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · exact fun h => ⟨h.2,h.1.2⟩
    · exact fun h => ⟨⟨u.property.1.trans_lt h.1,h.2⟩,h.1⟩
  rw [hs]

theorem rafteryKernel_zero_ae {a : ℝ} (ha : 0 < a) :
    rafteryKernel a 0 =ᵐ[volume] (fun _ => 0) := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with t ht
  have hn : ¬t ≤ 0 := fun h => ht (le_antisymm h bot_le)
  simp [rafteryKernel,hn,Real.zero_rpow ha.ne']

theorem integral_rafteryKernel {a : ℝ} (ha : 1 < a) (u : I) :
    (∫ t : I, rafteryKernel a u t) = (a*(u:ℝ)-(u:ℝ)^a)/(a-1) := by
  by_cases hu : (u:ℝ)=0
  · have hu' : u=0 := Subtype.ext hu
    subst u
    rw [integral_congr_ae (rafteryKernel_zero_ae (by linarith : 0<a))]
    simp [Real.zero_rpow (show a≠0 by linarith)]
  have hup : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm hu)
  have hl : (∫ t in Iic u, rafteryKernel a u t) = (u:ℝ) := by
    rw [setIntegral_congr_fun measurableSet_Iic (fun t ht =>
      show rafteryKernel a u t = 1 by simp [rafteryKernel,show t≤u from ht])]
    rw [Copula.integral_unit_Iic (fun _ => (1:ℝ))]
    simp
  have hr : (∫ t in Ioi u, rafteryKernel a u t) =
      (u:ℝ)^a*((1-(u:ℝ)^(-a+1))/(-a+1)) := by
    have he (t : I) (ht : t ∈ Ioi u) :
        rafteryKernel a u t = (u:ℝ)^a*(t:ℝ)^(-a) := by
      have hn : ¬t≤u := not_le.mpr ht
      simp only [rafteryKernel,hn,ite_false]
      rw [Real.div_rpow u.property.1 t.property.1, Real.rpow_neg t.property.1, div_eq_mul_inv]
    rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul,
      integral_unit_Ioi_real (fun t : ℝ => t^(-a)) u]
    have hz : (0:ℝ) ∉ uIcc (u:ℝ) 1 := by
      rw [uIcc_of_le u.property.2]
      simp only [mem_Icc, not_and_or]
      exact Or.inl (not_le.mpr hup)
    rw [integral_rpow (Or.inr ⟨by linarith, hz⟩), Real.one_rpow]
  have hs := integral_add_compl (s := Iic u) measurableSet_Iic
    (rafteryKernel_integrable (by linarith : 0≤a) u)
  rw [compl_Iic,hl,hr] at hs
  rw [← hs]
  have hp : (u:ℝ)^a*(u:ℝ)^(-a+1) = u := by
    rw [← Real.rpow_add hup]
    simp
  field_simp [show a-1≠0 by linarith, show -a+1≠0 by linarith]
  nlinarith [hp]

noncomputable def rafteryMixtureCDF (a : ℝ) (u v : I) : ℝ :=
  (u:ℝ)^a*(v:ℝ)^a/a + (a-1)/a * ∫ t : I, rafteryKernel a u t*rafteryKernel a v t

theorem rafteryMixtureCDF_symm (a : ℝ) (u v : I) :
    rafteryMixtureCDF a u v = rafteryMixtureCDF a v u := by
  unfold rafteryMixtureCDF
  simp only [mul_comm]

theorem rafteryMixtureCDF_zero {a : ℝ} (ha : 1<a) (v : I) :
    rafteryMixtureCDF a 0 v = 0 := by
  have hz : (∫ t : I, rafteryKernel a 0 t*rafteryKernel a v t) = 0 := by
    calc
      _ = ∫ _ : I, (0:ℝ) := integral_congr_ae (by
        filter_upwards [rafteryKernel_zero_ae (by linarith : 0<a)] with t ht
        rw [ht,zero_mul])
      _ = 0 := integral_zero _ _
  simp [rafteryMixtureCDF,hz,Real.zero_rpow (show a≠0 by linarith)]

theorem rafteryMixtureCDF_one {a : ℝ} (ha : 1<a) (u : I) :
    rafteryMixtureCDF a u 1 = u := by
  have hk (t : I) : rafteryKernel a 1 t = 1 := by
    simp only [rafteryKernel,show t≤1 from t.property.2,ite_true]
  unfold rafteryMixtureCDF
  simp_rw [hk,mul_one]
  rw [integral_rafteryKernel ha]
  simp only [show ((1:I):ℝ)=1 from rfl,Real.one_rpow,mul_one]
  field_simp [show a≠0 by linarith,show a-1≠0 by linarith]
  ring

theorem rafteryMixtureCDF_rectangle {a : ℝ} (ha : 1<a) (u₁ u₂ v₁ v₂ : I)
    (hu : u₁≤u₂) (hv : v₁≤v₂) :
    0 ≤ rafteryMixtureCDF a u₂ v₂-rafteryMixtureCDF a u₁ v₂-
      rafteryMixtureCDF a u₂ v₁+rafteryMixtureCDF a u₁ v₁ := by
  have ha0 : 0≤a := by linarith
  have hi := rafteryKernel_product_integrable ha0
  have hp : 0 ≤ ((u₂:ℝ)^a-(u₁:ℝ)^a)*((v₂:ℝ)^a-(v₁:ℝ)^a) :=
    mul_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow u₁.property.1 hu ha0))
      (sub_nonneg.mpr (Real.rpow_le_rpow v₁.property.1 hv ha0))
  have hk : 0 ≤ ∫ t : I,
      (rafteryKernel a u₂ t-rafteryKernel a u₁ t)*(rafteryKernel a v₂ t-rafteryKernel a v₁ t) := by
    apply integral_nonneg
    intro t
    exact mul_nonneg (sub_nonneg.mpr (rafteryKernel_monotone ha0 t hu))
      (sub_nonneg.mpr (rafteryKernel_monotone ha0 t hv))
  have he (t : I) :
      (rafteryKernel a u₂ t-rafteryKernel a u₁ t)*(rafteryKernel a v₂ t-rafteryKernel a v₁ t) =
      rafteryKernel a u₂ t*rafteryKernel a v₂ t-rafteryKernel a u₁ t*rafteryKernel a v₂ t-
        rafteryKernel a u₂ t*rafteryKernel a v₁ t+rafteryKernel a u₁ t*rafteryKernel a v₁ t := by ring
  simp_rw [he] at hk
  have hiA : Integrable (fun t => rafteryKernel a u₂ t*rafteryKernel a v₂ t-
      rafteryKernel a u₁ t*rafteryKernel a v₂ t) := (hi u₂ v₂).sub (hi u₁ v₂)
  have hiB : Integrable (fun t => rafteryKernel a u₂ t*rafteryKernel a v₂ t-
      rafteryKernel a u₁ t*rafteryKernel a v₂ t-rafteryKernel a u₂ t*rafteryKernel a v₁ t) :=
    hiA.sub (hi u₂ v₁)
  rw [integral_add hiB (hi u₁ v₁),
    integral_sub hiA (hi u₂ v₁),
    integral_sub (hi u₂ v₂) (hi u₁ v₂)] at hk
  have hh := add_nonneg (div_nonneg hp ha0)
    (mul_nonneg (div_nonneg (by linarith : 0≤a-1) ha0) hk)
  unfold rafteryMixtureCDF
  convert hh using 1
  ring

theorem rafteryMixture_isClassical {a : ℝ} (ha : 1<a) :
    IsClassical (fun x : Fin 2 → I => rafteryMixtureCDF a (x 0) (x 1)) := by
  apply IsClassical.ofBivariate (rafteryMixtureCDF a)
  · exact rafteryMixtureCDF_zero ha
  · intro u; rw [rafteryMixtureCDF_symm]; exact rafteryMixtureCDF_zero ha u
  · intro v; rw [rafteryMixtureCDF_symm]; exact rafteryMixtureCDF_one ha v
  · exact rafteryMixtureCDF_one ha
  · exact rafteryMixtureCDF_rectangle ha

noncomputable def rafteryPower (a : ℝ) (ha : 1<a) : Copula 2 :=
  ofClassical _ (rafteryMixture_isClassical ha)

theorem rafteryPower_cdf {a : ℝ} (ha : 1<a) (u v : I) :
    (rafteryPower a ha).cdf ![u,v] = rafteryMixtureCDF a u v := by
  rw [rafteryPower,cdf_ofClassical]
  rfl

theorem rafteryMixtureCDF_of_le {a : ℝ} (ha : 1<a) (u v : I) (huv : u≤v) :
    rafteryMixtureCDF a u v = (u:ℝ)+(u:ℝ)^a*((v:ℝ)^a-(v:ℝ)^(1-a))/(2*a-1) := by
  by_cases hv : (v:ℝ)=0
  · have hv' : v=0 := Subtype.ext hv
    have hu' : u=0 := le_antisymm (by simpa only [hv'] using huv) bot_le
    subst u; subst v
    rw [rafteryMixtureCDF_zero ha]
    simp [Real.zero_rpow (show a≠0 by linarith)]
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm hv)
  have ht (r : ℝ) (hr : r≠-1) : (∫ t in Ioi v, (t:ℝ)^r) =
      (1-(v:ℝ)^(r+1))/(r+1) := by
    rw [integral_unit_Ioi_real (fun t : ℝ => t^r) v,
      integral_rpow (Or.inr ⟨hr,by
        rw [uIcc_of_le v.property.2]
        exact fun h => (not_le.mpr hvp) h.1⟩), Real.one_rpow]
  have hku (t : I) (htv : t∈Ioi v) :
      rafteryKernel a u t = (u:ℝ)^a*(t:ℝ)^(-a) := by
    have hn : ¬t≤u := not_le.mpr (huv.trans_lt htv)
    simp only [rafteryKernel,hn,ite_false]
    rw [Real.div_rpow u.property.1 t.property.1,Real.rpow_neg t.property.1,div_eq_mul_inv]
  have hkv (t : I) (htv : t∈Ioi v) :
      rafteryKernel a v t = (v:ℝ)^a*(t:ℝ)^(-a) := by
    have hn : ¬t≤v := not_le.mpr htv
    simp only [rafteryKernel,hn,ite_false]
    rw [Real.div_rpow v.property.1 t.property.1,Real.rpow_neg t.property.1,div_eq_mul_inv]
  have hprod (t : I) (htv : t∈Ioi v) :
      rafteryKernel a u t*rafteryKernel a v t = (u:ℝ)^a*(v:ℝ)^a*(t:ℝ)^(-2*a) := by
    rw [hku t htv,hkv t htv,show -2*a=-a+-a by ring,
      Real.rpow_add (hvp.trans htv)]
    ring
  have hr₁ : (∫ t in Ioi v, rafteryKernel a u t) =
      (u:ℝ)^a*((1-(v:ℝ)^(-a+1))/(-a+1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hku,integral_const_mul,ht _ (by linarith)]
  have hr₂ : (∫ t in Ioi v, rafteryKernel a u t*rafteryKernel a v t) =
      (u:ℝ)^a*(v:ℝ)^a*((1-(v:ℝ)^(-2*a+1))/(-2*a+1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hprod,integral_const_mul,ht _ (by linarith)]
  have hl : (∫ t in Iic v, rafteryKernel a u t*rafteryKernel a v t) =
      ∫ t in Iic v, rafteryKernel a u t := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    have he : rafteryKernel a v t=1 := by simp [rafteryKernel,show t≤v from ht]
    change rafteryKernel a u t*rafteryKernel a v t = rafteryKernel a u t
    rw [he,mul_one]
  have hs₁ := integral_add_compl (s:=Iic v) measurableSet_Iic
    (rafteryKernel_integrable (by linarith : 0≤a) u)
  have hs₂ := integral_add_compl (s:=Iic v) measurableSet_Iic
    (rafteryKernel_product_integrable (by linarith : 0≤a) u v)
  rw [compl_Iic,hr₁,integral_rafteryKernel ha] at hs₁
  rw [compl_Iic,hl,hr₂] at hs₂
  have hi : (∫ t : I, rafteryKernel a u t*rafteryKernel a v t) =
      (a*(u:ℝ)-(u:ℝ)^a)/(a-1) -
      (u:ℝ)^a*((1-(v:ℝ)^(-a+1))/(-a+1)) +
      (u:ℝ)^a*(v:ℝ)^a*((1-(v:ℝ)^(-2*a+1))/(-2*a+1)) := by linarith
  have hp : (v:ℝ)^(-2*a+1) = (v:ℝ)^(1-a)/(v:ℝ)^a := by
    rw [← Real.rpow_sub hvp]
    congr 1; ring
  unfold rafteryMixtureCDF
  rw [hi,hp,show -a+1=1-a by ring]
  rw [show -2*a+1=-(2*a-1) by ring,show 1-a=-(a-1) by ring]
  simp only [div_neg]
  field_simp [show a≠0 by linarith,show a-1≠0 by linarith,
    show 1-a≠0 by linarith,show -2*a+1≠0 by linarith,
    show 2*a-1≠0 by linarith,(Real.rpow_pos_of_pos hvp a).ne']
  field_simp [show a*2-1≠0 by linarith]
  ring

end Verification
