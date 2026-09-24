import Verification.RafteryTP2
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

private theorem rafteryPower_cdf_error {a : ℝ} (ha : 1<a) (u v : I) (huv : u≤v) (hv : 0<(v:ℝ)) :
    (rafteryPower a ha).cdf ![u,v] =
      (u:ℝ)-(v:ℝ)*((u:ℝ)/(v:ℝ))^a*(∫ t in (v:ℝ)..1, t^(2*a-2)) := by
  rw [rafteryPower_cdf,rafteryMixtureCDF_of_le ha u v huv,
    integral_rpow (Or.inl (by linarith : -1<2*a-2)),Real.one_rpow]
  rw [show 2*a-2+1=2*a-1 by ring]
  have hp : (v:ℝ)^(2*a-1) = (v:ℝ)^a*(v:ℝ)^a/(v:ℝ) := by
    rw [Real.rpow_sub hv,show 2*a=a+a by ring,Real.rpow_add hv,Real.rpow_one]
  rw [hp,Real.div_rpow u.property.1 v.property.1,Real.rpow_sub hv,Real.rpow_one]
  field_simp [hv.ne',(Real.rpow_pos_of_pos hv a).ne',show 2*a-1≠0 by linarith]
  ring

private theorem rafteryPower_cdf_monotone_of_le {a b : ℝ} (ha : 1<a) (hab : a≤b)
    (u v : I) (huv : u≤v) :
    (rafteryPower a ha).cdf ![u,v] ≤ (rafteryPower b (ha.trans_le hab)).cdf ![u,v] := by
  by_cases hv0 : (v:ℝ)=0
  · have hv : v=0 := Subtype.ext hv0
    have hu : u=0 := le_antisymm (by simpa only [hv] using huv) bot_le
    subst u; simp only [cdf_two_zero_left,le_refl]
  have hv : 0<(v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm hv0)
  have hqa : 0≤2*a-2 := by linarith
  have hqb : 0≤2*b-2 := by linarith
  have hia := (Real.continuous_rpow_const hqa).intervalIntegrable (μ:=volume) (v:ℝ) 1
  have hib := (Real.continuous_rpow_const hqb).intervalIntegrable (μ:=volume) (v:ℝ) 1
  have hi : (∫ t in (v:ℝ)..1, t^(2*b-2)) ≤ ∫ t in (v:ℝ)..1, t^(2*a-2) := by
    apply intervalIntegral.integral_mono_on v.property.2 hib hia
    intro t ht
    exact Real.rpow_le_rpow_of_exponent_ge (hv.trans_le ht.1) ht.2 (by linarith)
  have hin : 0≤∫ t in (v:ℝ)..1, t^(2*b-2) :=
    intervalIntegral.integral_nonneg v.property.2 (fun t ht => Real.rpow_nonneg (hv.le.trans ht.1) _)
  have hratio : ((u:ℝ)/(v:ℝ))^b ≤ ((u:ℝ)/(v:ℝ))^a :=
    Real.rpow_le_rpow_of_exponent_ge' (div_nonneg u.property.1 v.property.1)
      ((div_le_one hv).mpr huv) (by linarith) hab
  have hm := mul_le_mul hratio hi hin (Real.rpow_nonneg (div_nonneg u.property.1 v.property.1) _)
  have hh := mul_le_mul_of_nonneg_left hm v.property.1
  rw [rafteryPower_cdf_error ha u v huv hv,
    rafteryPower_cdf_error (ha.trans_le hab) u v huv hv]
  nlinarith only [hh]

theorem rafteryPower_lowerOrthant_monotone {a b : ℝ} (ha : 1<a) (hab : a≤b) :
    (rafteryPower a ha).LowerOrthantLE (rafteryPower b (ha.trans_le hab)) := by
  intro x
  have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  by_cases h : x 0≤x 1
  · exact rafteryPower_cdf_monotone_of_le ha hab _ _ h
  · have he (c : ℝ) (hc : 1<c) : (rafteryPower c hc).cdf ![x 0,x 1] =
        (rafteryPower c hc).cdf ![x 1,x 0] := by
      rw [rafteryPower_cdf,rafteryPower_cdf,rafteryMixtureCDF_symm]
    rw [he,he]
    exact rafteryPower_cdf_monotone_of_le ha hab _ _ (le_of_not_ge h)

theorem raftery_lowerOrthant_monotone {δ η : I} (hδη : δ≤η) :
    (raftery δ).LowerOrthantLE (raftery η) := by
  by_cases hδ0 : δ=0
  · subst δ; rw [raftery_zero]
    exact (isPQD_iff_lowerOrthantLE _).mp (raftery_isPQD η)
  by_cases hη1 : η=1
  · subst η; rw [raftery_one]; exact lowerOrthantLE_comonotonic _
  have hη0 : η≠0 := by
    intro he
    exact hδ0 (le_antisymm (by simpa only [he] using hδη) bot_le)
  have hδ1 : δ≠1 := by
    intro he
    exact hη1 (le_antisymm η.property.2 (by simpa only [he] using hδη))
  have hdδ : 0<1-(δ:ℝ) := sub_pos.mpr
    (lt_of_le_of_ne δ.property.2 (fun h => hδ1 (Subtype.ext h)))
  have hdη : 0<1-(η:ℝ) := sub_pos.mpr
    (lt_of_le_of_ne η.property.2 (fun h => hη1 (Subtype.ext h)))
  have hab : 1/(1-(δ:ℝ)) ≤ 1/(1-(η:ℝ)) :=
    (div_le_div_iff₀ hdδ hdη).mpr (by nlinarith [show (δ:ℝ)≤η from hδη])
  simp only [raftery,hδ0,hδ1,hη0,hη1,dite_false]
  exact rafteryPower_lowerOrthant_monotone (raftery_shape_gt_one δ hδ0 hδ1) hab

theorem raftery_schur_monotone {δ η : I} (hδη : δ≤η) :
    (raftery δ).SchurBothLE (raftery η) := by
  have ho := raftery_lowerOrthant_monotone hδη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (raftery_isCI δ).1 (raftery_isCI η).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (raftery_isCI δ).2 (raftery_isCI η).2).mpr
    intro x
    have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_transpose,cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
