import Verification.ExtremeValuePowerConstruction
import Papers.AnsariRockel2024.BB5Submodular

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

noncomputable def bb5 (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ) : Copula 2 :=
  extremeValuePower (galambos δ hδ) (Papers.AnsariRockel2024.galambos_isExtremeValue δ hδ) θ hθ

end Verification

namespace Papers.AnsariRockel2024

theorem bb5_cdf_interior (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ) (u v : I)
    (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (Verification.bb5 θ δ hθ hδ).cdf ![u,v]=
      Real.exp (-Verification.bb5TailKernel θ δ (-Real.log (u:ℝ)) (-Real.log (v:ℝ))) := by
  rw [Verification.bb5,Verification.extremeValuePower_cdf,
    Verification.extremeValuePowerCDF_positive_coords _ _ _ _ hu.1 hv.1,
    bb5_exponent_eq_power_log θ δ _ _ hδ
      (neg_pos.mpr (Real.log_neg hu.1 hu.2)) (neg_pos.mpr (Real.log_neg hv.1 hv.2))]

theorem bb5_cdf_full (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ) (u v : I) :
    (Verification.bb5 θ δ hθ hδ).cdf ![u,v]=
      if u=0 ∨ v=0 then 0 else if u=1 then (v:ℝ) else if v=1 then (u:ℝ)
      else Real.exp (-(((-Real.log (u:ℝ))^θ+(-Real.log (v:ℝ))^θ-
        (((-Real.log (u:ℝ))^(-δ*θ)+(-Real.log (v:ℝ))^(-δ*θ))^(-1/δ)))^(1/θ))) := by
  by_cases hz : u=0 ∨ v=0
  · rw [ite_eq_left hz,Verification.bb5,Verification.extremeValuePower_cdf]
    exact ite_eq_left hz
  rw [ite_eq_right hz]
  by_cases hu1 : u=1
  · rw [ite_eq_left hu1,hu1,Verification.bb5,Verification.extremeValuePower_cdf,
      Verification.extremeValuePowerCDF_one_left _ _ (by linarith)]
  rw [ite_eq_right hu1]
  by_cases hv1 : v=1
  · rw [ite_eq_left hv1,hv1,Verification.bb5,Verification.extremeValuePower_cdf,
      Verification.extremeValuePowerCDF_one_right _ _ (by linarith)]
  rw [ite_eq_right hv1]
  have hu : (u:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne u.property.1 (fun h => hz (Or.inl (Subtype.ext h.symm))),
      lt_of_le_of_ne u.property.2 (fun h => hu1 (Subtype.ext h))⟩
  have hv : (v:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne v.property.1 (fun h => hz (Or.inr (Subtype.ext h.symm))),
      lt_of_le_of_ne v.property.2 (fun h => hv1 (Subtype.ext h))⟩
  rw [bb5_cdf_interior θ δ hθ hδ u v hu hv,Verification.bb5TailKernel_formula]
  · exact neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2)
  · exact neg_nonneg.mpr (Real.log_nonpos v.property.1 v.property.2)

end Papers.AnsariRockel2024
