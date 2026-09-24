import Verification.Raftery
import Copula.Rank.Integration

open ProbabilityTheory Copula Filter
open scoped unitInterval Topology

namespace Verification

/-- A uniform CDF error bound at the comonotonic endpoint. -/
theorem raftery_comonotonic_bounds (δ u v : I) :
    min (u:ℝ) v - (1-(δ:ℝ)) ≤ (raftery δ).cdf ![u,v] ∧
      (raftery δ).cdf ![u,v] ≤ min (u:ℝ) v := by
  have hupper : (raftery δ).cdf ![u,v] ≤ min (u:ℝ) v :=
    le_min ((raftery δ).cdf_le_coord ![u,v] 0) ((raftery δ).cdf_le_coord ![u,v] 1)
  refine ⟨?_,hupper⟩
  by_cases h1 : δ=1
  · subst δ
    rw [raftery_one,cdf_comonotonic_two]
    simp
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr
    (lt_of_le_of_ne δ.property.2 (fun h => h1 (Subtype.ext h)))
  have hp : 0<1+(δ:ℝ) := by linarith [δ.property.1]
  let a : ℝ := 1/(1-(δ:ℝ))
  let q : ℝ := -(δ:ℝ)/(1-(δ:ℝ))
  let k : ℝ := (1-(δ:ℝ))/(1+(δ:ℝ))
  have ha : 0<a := one_div_pos.mpr hd
  have hk : 0≤k := div_nonneg hd.le hp.le
  have hkle : k≤1-(δ:ℝ) := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [mul_nonneg δ.property.1 hd.le]
  have hm : 0≤min (u:ℝ) v := le_min u.property.1 v.property.1
  have hM : 0≤max (u:ℝ) v := u.property.1.trans (le_max_left _ _)
  have hpow : (min (u:ℝ) v)^a*(max (u:ℝ) v)^q ≤ 1 := by
    by_cases hzero : max (u:ℝ) v=0
    · have hmzero : min (u:ℝ) v=0 := le_antisymm ((min_le_max).trans_eq hzero) hm
      simp only [hmzero,Real.zero_rpow ha.ne',zero_mul]
      norm_num
    have hpos : 0<max (u:ℝ) v := lt_of_le_of_ne hM (Ne.symm hzero)
    have he : a+q=1 := by dsimp [a,q]; field_simp; ring
    calc
      _ ≤ (max (u:ℝ) v)^a*(max (u:ℝ) v)^q := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hm min_le_max ha.le) (Real.rpow_nonneg hM _)
      _ = max (u:ℝ) v := by rw [← Real.rpow_add hpos,he,Real.rpow_one]
      _ ≤ 1 := max_le u.property.2 v.property.2
  have hn := mul_nonneg hk (mul_nonneg (Real.rpow_nonneg hm a) (Real.rpow_nonneg hM a))
  have hb := mul_le_mul_of_nonneg_left hpow hk
  rw [raftery_cdf δ h1]
  change min (u:ℝ) v-(1-(δ:ℝ)) ≤ min (u:ℝ) v+k*(min (u:ℝ) v)^a*
    ((max (u:ℝ) v)^a-(max (u:ℝ) v)^q)
  nlinarith [hn,hb]

theorem raftery_tendsto_one {A : Type*} {l : Filter A} (δ : A → I)
    (hδ : Tendsto (fun x => (δ x : ℝ)) l (𝓝 1)) (u v : I) :
    Tendsto (fun x => (raftery (δ x)).cdf ![u,v]) l
      (𝓝 ((comonotonic 2).cdf ![u,v])) := by
  rw [cdf_comonotonic_two]
  have hlo : Tendsto (fun x => min (u:ℝ) v-(1-(δ x:ℝ))) l (𝓝 (min (u:ℝ) v)) := by
    simpa using (tendsto_const_nhds (x:=min (u:ℝ) v)).sub
      ((tendsto_const_nhds (x:=(1:ℝ))).sub hδ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun x => (raftery_comonotonic_bounds (δ x) u v).1)
    (fun x => (raftery_comonotonic_bounds (δ x) u v).2)

/-- Continuous parameter dependence on the entire closed parameter interval and closed square. -/
theorem raftery_tendsto_parameter {A : Type*} {l : Filter A} (δ : A → I) (η : I)
    (hδ : Tendsto (fun x => (δ x:ℝ)) l (𝓝 (η:ℝ))) (u v : I) :
    Tendsto (fun x => (raftery (δ x)).cdf ![u,v]) l (𝓝 ((raftery η).cdf ![u,v])) := by
  by_cases hη : η=1
  · subst η
    rw [raftery_one]
    exact raftery_tendsto_one δ hδ u v
  by_cases hu : u=0
  · subst u; simp only [cdf_two_zero_left]; exact tendsto_const_nhds
  by_cases hv : v=0
  · subst v
    have he (C : Copula 2) : C.cdf ![u,0]=0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 (by simp)
    simp only [he]; exact tendsto_const_nhds
  have hup : 0<(u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hvp : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have hm : min (u:ℝ) v ≠ 0 := (lt_min hup hvp).ne'
  have hM : max (u:ℝ) v ≠ 0 := (hup.trans_le (le_max_left _ _)).ne'
  have hηlt : (η:ℝ)<1 := lt_of_le_of_ne η.property.2 (fun h => hη (Subtype.ext h))
  have hd : 1-(η:ℝ)≠0 := (sub_pos.mpr hηlt).ne'
  have hp : 1+(η:ℝ)≠0 := by linarith [η.property.1]
  have hden : ContinuousAt (fun x : ℝ => 1-x) (η:ℝ) := continuousAt_const.sub continuousAt_id
  have hplus : ContinuousAt (fun x : ℝ => 1+x) (η:ℝ) := continuousAt_const.add continuousAt_id
  have ha : ContinuousAt (fun x : ℝ => 1/(1-x)) (η:ℝ) := continuousAt_const.div hden hd
  have hq : ContinuousAt (fun x : ℝ => -x/(1-x)) (η:ℝ) := continuousAt_id.neg.div hden hd
  have hc : ContinuousAt (fun x : ℝ => min (u:ℝ) v + (1-x)/(1+x)*
      (min (u:ℝ) v)^(1/(1-x))*((max (u:ℝ) v)^(1/(1-x))-(max (u:ℝ) v)^(-x/(1-x)))) (η:ℝ) :=
    continuousAt_const.add (((hden.div hplus hp).mul
      (continuousAt_const.rpow ha (Or.inl hm))).mul
        ((continuousAt_const.rpow ha (Or.inl hM)).sub (continuousAt_const.rpow hq (Or.inl hM))))
  have hevent : ∀ᶠ x in l, (δ x:ℝ)<1 := (tendsto_order.1 hδ).2 1 hηlt
  rw [raftery_cdf η hη]
  apply (hc.tendsto.comp hδ).congr'
  filter_upwards [hevent] with x hx
  exact (raftery_cdf (δ x) (fun h => (ne_of_lt hx) (congrArg Subtype.val h)) u v).symm

theorem raftery_tendsto_zero {A : Type*} {l : Filter A} (δ : A → I)
    (hδ : Tendsto (fun x => (δ x:ℝ)) l (𝓝 0)) (u v : I) :
    Tendsto (fun x => (raftery (δ x)).cdf ![u,v]) l
      (𝓝 ((independence 2).cdf ![u,v])) := by
  simpa only [raftery_zero] using raftery_tendsto_parameter δ 0 hδ u v

end Verification
