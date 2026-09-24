import Verification.RafteryDensity
import Verification.MTP2ConditionalIncreasing
import Verification.MarshallOlkinSingular
import Verification.RafteryRho
import Copula.Order.StrictSpearman
import Verification.MarshallOlkinOrder

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

private noncomputable def rafteryMaxFactor (a t : ℝ) : ℝ := a+(a-1)*t^(1-2*a)

private theorem rafteryMaxFactor_nonneg {a t : ℝ} (ha : 1<a) (ht : 0≤t) :
    0≤rafteryMaxFactor a t :=
  add_nonneg (by linarith) (mul_nonneg (by linarith) (Real.rpow_nonneg ht _))

private theorem rafteryMaxFactor_antitone {a : ℝ} (ha : 1<a) :
    AntitoneOn (rafteryMaxFactor a) (Ioi 0) := by
  intro x hx y _ hxy
  unfold rafteryMaxFactor
  exact add_le_add_right (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (show 0<x from hx) hxy (by linarith : 1-2*a≤0))
    (by linarith : 0≤a-1)) a

private theorem rafteryDensity_factor {a u v : ℝ} (hu : 0<u) :
    rafteryDensity a u v = a/(2*a-1)*u^(a-1)*v^(a-1)*rafteryMaxFactor a (max u v) := by
  have hprod : u^(a-1)*v^(a-1) = (min u v)^(a-1)*(max u v)^(a-1) := by
    by_cases h : u≤v
    · rw [min_eq_left h,max_eq_right h]
    · rw [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h)]; ring
  have hp : (max u v)^(a-1)*(max u v)^(1-2*a) = (max u v)^(-a) := by
    rw [← Real.rpow_add (hu.trans_le (le_max_left _ _))]
    congr 1; ring
  unfold rafteryDensity rafteryMaxFactor
  calc
    _ = a/(2*a-1)*(min u v)^(a-1)*
        (a*(max u v)^(a-1)+(a-1)*((max u v)^(a-1)*(max u v)^(1-2*a))) := by rw [hp]
    _ = a/(2*a-1)*((min u v)^(a-1)*(max u v)^(a-1))*(a+(a-1)*(max u v)^(1-2*a)) := by ring
    _ = _ := by rw [← hprod]; ring

private theorem raftery_max_minor {a x₁ x₂ y₁ y₂ : ℝ} (ha : 1<a)
    (hx : 0<x₁) (hy : 0<y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    rafteryMaxFactor a (max x₁ y₂)*rafteryMaxFactor a (max x₂ y₁) ≤
      rafteryMaxFactor a (max x₁ y₁)*rafteryMaxFactor a (max x₂ y₂) := by
  have hm := rafteryMaxFactor_antitone ha
  by_cases h : x₂≤y₂
  · rw [max_eq_right (hxx.trans h),max_eq_right h]
    have hc := hm (hx.trans_le (le_max_left x₁ y₁)) (hx.trans_le (hxx.trans (le_max_left x₂ y₁)))
      (max_le_max hxx le_rfl)
    exact (mul_le_mul_of_nonneg_left hc (rafteryMaxFactor_nonneg ha (hy.le.trans hyy))).trans_eq (mul_comm _ _)
  · have h' : y₂≤x₂ := le_of_not_ge h
    rw [max_eq_left h',max_eq_left (hyy.trans h')]
    have hc := hm (hx.trans_le (le_max_left x₁ y₁)) (hx.trans_le (le_max_left x₁ y₂))
      (max_le_max le_rfl hyy)
    exact mul_le_mul_of_nonneg_right hc (rafteryMaxFactor_nonneg ha (hx.le.trans hxx))

theorem rafteryDensity_zero {a : ℝ} (ha : 1<a) (v : I) : rafteryDensity a 0 v=0 := by
  simp only [rafteryDensity,min_eq_left v.property.1,Real.zero_rpow (sub_pos.mpr ha).ne',mul_zero,zero_mul]

theorem rafteryDensity_symm (a u v : ℝ) : rafteryDensity a u v=rafteryDensity a v u := by
  simp only [rafteryDensity,min_comm,max_comm]

theorem rafteryDensity_isTP2 {a : ℝ} (ha : 1<a) :
    IsTP2 (fun u v : I => rafteryDensity a u v) := by
  intro x₁ x₂ y₁ y₂ hxx hyy
  change rafteryDensity a x₁ y₂*rafteryDensity a x₂ y₁ ≤
    rafteryDensity a x₁ y₁*rafteryDensity a x₂ y₂
  by_cases hx0 : x₁=0
  · subst x₁
    simp only [show ((0:I):ℝ)=0 from rfl,rafteryDensity_zero ha,zero_mul,le_refl]
  by_cases hy0 : y₁=0
  · subst y₁
    have he (t : I) : rafteryDensity a t 0=0 := by rw [rafteryDensity_symm,rafteryDensity_zero ha]
    simp only [show ((0:I):ℝ)=0 from rfl,he,mul_zero,zero_mul,le_refl]
  have hx : 0<(x₁:ℝ) := lt_of_le_of_ne x₁.property.1 (Ne.symm (fun h => hx0 (Subtype.ext h)))
  have hy : 0<(y₁:ℝ) := lt_of_le_of_ne y₁.property.1 (Ne.symm (fun h => hy0 (Subtype.ext h)))
  have hx₂ : 0<(x₂:ℝ) := hx.trans_le hxx
  have hc := raftery_max_minor ha hx hy hxx hyy
  have hw : 0≤(a/(2*a-1))^2*(x₁:ℝ)^(a-1)*(x₂:ℝ)^(a-1)*(y₁:ℝ)^(a-1)*(y₂:ℝ)^(a-1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg x₁.property.1 _)) (Real.rpow_nonneg x₂.property.1 _))
        (Real.rpow_nonneg y₁.property.1 _)) (Real.rpow_nonneg y₂.property.1 _)
  have hh := mul_le_mul_of_nonneg_left hc hw
  rw [rafteryDensity_factor hx,rafteryDensity_factor hx₂,
    rafteryDensity_factor hx,rafteryDensity_factor hx₂]
  convert hh using 1 <;> ring

theorem raftery_hasMTP2Density (δ : I) (h1 : δ≠1) : (raftery δ).HasMTP2Density := by
  by_cases h0 : δ=0
  · subst δ; rw [raftery_zero]; exact hasMTP2Density_independence 2
  have ha := raftery_shape_gt_one δ h0 h1
  refine ⟨fun x => rafteryDensity (1/(1-(δ:ℝ))) (x 0) (x 1),?_,?_,?_,raftery_toMeasure_density δ h1⟩
  · unfold rafteryDensity; fun_prop
  · intro x; exact rafteryDensity_nonneg ha.le (x 0) (x 1)
  · exact (isMTP2_fin_two_iff _).mpr (rafteryDensity_isTP2 ha)

theorem raftery_absolutelyContinuous_iff (δ : I) :
    (raftery δ).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ δ≠1 := by
  refine ⟨?_,raftery_absolutelyContinuous δ⟩
  intro h hδ
  subst δ
  rw [raftery_one,← marshallOlkin_one_one] at h
  have hh := (marshallOlkin_absolutelyContinuous_iff 1 1).mp h
  norm_num at hh

theorem raftery_density_tp2_iff (δ : I) : (raftery δ).HasMTP2Density ↔ δ≠1 :=
  ⟨fun h => (raftery_absolutelyContinuous_iff δ).mp h.absolutelyContinuous,
    raftery_hasMTP2Density δ⟩

theorem raftery_isCI (δ : I) : (raftery δ).IsCI := by
  by_cases h1 : δ=1
  · subst δ; rw [raftery_one]; exact isCI_comonotonic
  · exact mtp2_isCI (raftery_hasMTP2Density δ h1)

theorem raftery_printed_tp2_exclusion_false :
    ¬∀ δ : I, raftery δ≠independence 2 → ¬(raftery δ).HasMTP2Density := by
  intro h
  let δ : I := ⟨1/2,by norm_num⟩
  have hn : raftery δ≠independence 2 := by
    intro he
    have hr := raftery_spearmanRho δ
    rw [he,spearmanRho_independence] at hr
    norm_num [δ] at hr
  have h1 : δ≠1 := by intro he; have hh := congrArg Subtype.val he; norm_num [δ] at hh
  exact h δ hn (raftery_hasMTP2Density δ h1)

theorem raftery_isPQD (δ : I) : (raftery δ).IsPQD := (raftery_isCI δ).isPQD

theorem raftery_nqd_iff (δ : I) : (raftery δ).IsNQD ↔ δ=0 := by
  constructor
  · intro h
    by_contra hn
    have hd : 0<(δ:ℝ) := lt_of_le_of_ne δ.property.1 (Ne.symm (fun he => hn (Subtype.ext he)))
    have hr := h.spearmanRho_nonpos
    rw [raftery_spearmanRho] at hr
    have hp : 0<(δ:ℝ)*(4-3*(δ:ℝ))/(2-(δ:ℝ))^2 :=
      div_pos (mul_pos hd (by linarith [δ.property.2])) (sq_pos_of_pos (by linarith [δ.property.2]))
    linarith
  · rintro rfl
    rw [raftery_zero]
    exact isCD_independence.isNQD

theorem raftery_cd_iff (δ : I) : (raftery δ).IsCD ↔ δ=0 := by
  refine ⟨fun h => (raftery_nqd_iff δ).mp h.isNQD,?_⟩
  rintro rfl
  rw [raftery_zero]
  exact isCD_independence

end Verification
