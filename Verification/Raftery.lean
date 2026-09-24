import Verification.RafteryMixture
import Copula.TailDependence.Examples

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem rafteryPower_cdf_min {a : ℝ} (ha : 1<a) (u v : I) :
    (rafteryPower a ha).cdf ![u,v] =
      min (u:ℝ) v + (min (u:ℝ) v)^a*((max (u:ℝ) v)^a-(max (u:ℝ) v)^(1-a))/(2*a-1) := by
  rw [rafteryPower_cdf]
  by_cases huv : (u:ℝ)≤v
  · rw [min_eq_left huv,max_eq_right huv]
    exact rafteryMixtureCDF_of_le ha u v huv
  · have hvu := le_of_not_ge huv
    rw [min_eq_right hvu,max_eq_left hvu,rafteryMixtureCDF_symm]
    exact rafteryMixtureCDF_of_le ha v u hvu

theorem raftery_shape_gt_one (δ : I) (h0 : δ≠0) (h1 : δ≠1) :
    1 < 1/(1-(δ:ℝ)) := by
  have hd0 : 0<(δ:ℝ) := lt_of_le_of_ne δ.property.1 (Ne.symm (fun h => h0 (Subtype.ext h)))
  have hd1 : (δ:ℝ)<1 := lt_of_le_of_ne δ.property.2 (fun h => h1 (Subtype.ext h))
  apply (lt_div_iff₀ (sub_pos.mpr hd1)).mpr
  linarith

/-- The corrected Raftery copula, including its two endpoint measures. -/
noncomputable def raftery (δ : I) : Copula 2 :=
  if h0 : δ=0 then independence 2 else
  if h1 : δ=1 then comonotonic 2 else
    rafteryPower (1/(1-(δ:ℝ))) (raftery_shape_gt_one δ h0 h1)

theorem raftery_zero : raftery 0 = independence 2 := by simp [raftery]

theorem raftery_one : raftery 1 = comonotonic 2 := by simp [raftery]

theorem raftery_cdf_interior (δ : I) (h0 : δ≠0) (h1 : δ≠1) (u v : I) :
    (raftery δ).cdf ![u,v] = min (u:ℝ) v +
      (1-(δ:ℝ))/(1+(δ:ℝ)) * (min (u:ℝ) v)^(1/(1-(δ:ℝ))) *
        ((max (u:ℝ) v)^(1/(1-(δ:ℝ))) - (max (u:ℝ) v)^(-(δ:ℝ)/(1-(δ:ℝ)))) := by
  simp only [raftery,h0,h1,dite_false]
  rw [rafteryPower_cdf_min]
  have hd : 1-(δ:ℝ)≠0 := sub_ne_zero.mpr (fun h => h1 (Subtype.ext h.symm))
  have he : 1-1/(1-(δ:ℝ)) = -(δ:ℝ)/(1-(δ:ℝ)) := by field_simp; ring
  rw [he]
  have hp : 1+(δ:ℝ)≠0 := by linarith [δ.property.1]
  have hden : 2*(1/(1-(δ:ℝ)))-1 = (1+(δ:ℝ))/(1-(δ:ℝ)) := by field_simp; ring
  rw [hden]
  field_simp [hd,hp]

/-- Correctly normalized full-square CDF for every parameter below the comonotonic endpoint. -/
theorem raftery_cdf (δ : I) (h1 : δ≠1) (u v : I) :
    (raftery δ).cdf ![u,v] = min (u:ℝ) v +
      (1-(δ:ℝ))/(1+(δ:ℝ)) * (min (u:ℝ) v)^(1/(1-(δ:ℝ))) *
        ((max (u:ℝ) v)^(1/(1-(δ:ℝ))) - (max (u:ℝ) v)^(-(δ:ℝ)/(1-(δ:ℝ)))) := by
  by_cases h0 : δ=0
  · subst δ
    rw [raftery_zero]
    norm_num [cdf_independence,Fin.prod_univ_two]
    nlinarith [min_mul_max (u:ℝ) (v:ℝ)]
  · exact raftery_cdf_interior δ h0 h1 u v

/-- The source CDF with its missing normalization factor restored. -/
theorem raftery_cdf_corrected (δ : I) (h1 : δ≠1) (u v : I) :
    (raftery δ).cdf ![u,v] = min (u:ℝ) v +
      (1-(δ:ℝ))/(1+(δ:ℝ)) * ((u:ℝ)*(v:ℝ))^(1/(1-(δ:ℝ))) *
        (1-(max (u:ℝ) v)^(-(1+(δ:ℝ))/(1-(δ:ℝ)))) := by
  have hd : 0<1-(δ:ℝ) := sub_pos.mpr
    (lt_of_le_of_ne δ.property.2 (fun h => h1 (Subtype.ext h)))
  rw [raftery_cdf δ h1]
  by_cases hm : max (u:ℝ) v = 0
  · have hu : (u:ℝ)=0 := le_antisymm ((le_max_left _ _).trans_eq hm) u.property.1
    have hv : (v:ℝ)=0 := le_antisymm ((le_max_right _ _).trans_eq hm) v.property.1
    simp only [hu,hv,min_self,max_self,zero_mul,
      Real.zero_rpow (ne_of_gt (one_div_pos.mpr hd)),mul_zero,zero_add]
  have hmp : 0<max (u:ℝ) v := lt_of_le_of_ne
    (u.property.1.trans (le_max_left _ _)) (Ne.symm hm)
  have hb : ((u:ℝ)*(v:ℝ))^(1/(1-(δ:ℝ))) =
      (min (u:ℝ) v)^(1/(1-(δ:ℝ)))*(max (u:ℝ) v)^(1/(1-(δ:ℝ))) := by
    rw [← min_mul_max (u:ℝ) (v:ℝ),Real.mul_rpow (le_min u.property.1 v.property.1) hmp.le]
  have he : 1/(1-(δ:ℝ)) + -(1+(δ:ℝ))/(1-(δ:ℝ)) = -(δ:ℝ)/(1-(δ:ℝ)) := by ring
  have hp := Real.rpow_add hmp (1/(1-(δ:ℝ))) (-(1+(δ:ℝ))/(1-(δ:ℝ)))
  rw [he] at hp
  rw [hb,hp]
  ring

end Verification
