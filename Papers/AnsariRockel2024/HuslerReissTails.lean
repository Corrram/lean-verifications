import Papers.AnsariRockel2024.HuslerReiss
import Verification.PickandsDiagonal

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem huslerReiss_extremalCoefficient (δ : ℝ) (hδ : 0<δ) :
    (Verification.huslerReissPositive δ hδ).extremalCoefficient=
      2*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ) := by
  rw [Verification.extremalCoefficient_eq_twice_pickands _
    (Verification.huslerReissPositive_isExtremeValue δ hδ),
    huslerReiss_pickands_interior δ hδ unitHalf (by norm_num [unitHalf])]
  norm_num [unitHalf]
  ring

theorem huslerReiss_tails (δ : ℝ) (hδ : 0<δ) :
    (Verification.huslerReissPositive δ hδ).HasLowerTailDependence 0 ∧
    (Verification.huslerReissPositive δ hδ).HasUpperTailDependence
      (2-2*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ)) := by
  have hp := (Verification.huslerReissPositive_isExtremeValue δ hδ).hasPowerDiagonal
  rw [huslerReiss_extremalCoefficient δ hδ] at hp
  have h := Verification.standardNormalCDF_strictMono (one_div_pos.mpr hδ)
  rw [Verification.standardGaussian_cdf_zero] at h
  exact ⟨hp.hasLowerTailDependence_zero (by linarith),hp.hasUpperTailDependence⟩

end Papers.AnsariRockel2024
