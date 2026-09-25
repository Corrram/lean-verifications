import Papers.AnsariRockel2024.GalambosDependence
import Copula.ExtremeValue.Diagonal

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

private theorem galambos_exponent_gt_one (δ : ℝ) (hδ : 0<δ) :
    1<2-(2:ℝ)^(-1/δ) := by
  have h : (2:ℝ)^(-1/δ)<(2:ℝ)^(0:ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) (div_neg_of_neg_of_pos (by norm_num : (-1:ℝ)<0) hδ)
  rw [Real.rpow_zero] at h
  linarith

theorem galambos_power_diagonal (δ : ℝ) (hδ : 0<δ) :
    (Verification.galambos δ hδ).HasPowerDiagonal (2-(2:ℝ)^(-1/δ)) := by
  intro t
  by_cases h0 : t=0
  · simp [h0,Real.zero_rpow (show 2-(2:ℝ)^(-1/δ)≠0 by linarith [galambos_exponent_gt_one δ hδ])]
  by_cases h1 : t=1
  · simp [h1]
  have ht : (t:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne t.property.1 (fun h => h0 (Subtype.ext h.symm)),
      lt_of_le_of_ne t.property.2 (fun h => h1 (Subtype.ext h))⟩
  have hl : 0≤-Real.log (t:ℝ) := (neg_pos.mpr (Real.log_neg ht.1 ht.2)).le
  rw [Copula.diagonal,galambos_cdf_interior δ hδ t t ht ht,← two_mul,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hl _),
    ← Real.rpow_mul hl,show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one]
  rw [Real.rpow_def_of_pos ht.1]
  nth_rw 1 [← Real.exp_log ht.1]
  nth_rw 2 [← Real.exp_log ht.1]
  rw [← Real.exp_add,← Real.exp_add]
  congr 1
  ring

theorem galambos_extremalCoefficient (δ : ℝ) (hδ : 0<δ) :
    (Verification.galambos δ hδ).extremalCoefficient=2-(2:ℝ)^(-1/δ) :=
  (galambos_power_diagonal δ hδ).extremalCoefficient_eq

theorem galambos_tails (δ : ℝ) (hδ : 0<δ) :
    (Verification.galambos δ hδ).HasLowerTailDependence 0 ∧
    (Verification.galambos δ hδ).HasUpperTailDependence ((2:ℝ)^(-1/δ)) := by
  constructor
  · exact (galambos_power_diagonal δ hδ).hasLowerTailDependence_zero (galambos_exponent_gt_one δ hδ)
  · simpa only [sub_sub_cancel] using (galambos_power_diagonal δ hδ).hasUpperTailDependence

end Papers.AnsariRockel2024
