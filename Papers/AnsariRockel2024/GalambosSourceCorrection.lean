import Papers.AnsariRockel2024.GalambosTails
import Verification.PickandsDiagonal

open ProbabilityTheory Real Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem galambos_pickands_midpoint (δ : ℝ) (hδ : 0<δ) :
    Verification.copulaPickands (Verification.galambos δ hδ) unitHalf=
      1-(2:ℝ)^(-1/δ)/2 := by
  have h := Verification.extremalCoefficient_eq_twice_pickands _ (galambos_isExtremeValue δ hδ)
  rw [galambos_extremalCoefficient] at h
  linarith

theorem galambos_pickands_midpoint_gt_half (δ : ℝ) (hδ : 0<δ) :
    (1/2:ℝ)<Verification.copulaPickands (Verification.galambos δ hδ) unitHalf := by
  rw [galambos_pickands_midpoint]
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    (div_neg_of_neg_of_pos (by norm_num : (-1:ℝ)<0) hδ)
  rw [Real.rpow_zero] at h
  linarith

theorem galambos_printed_midpoint_counterexample :
    Verification.copulaPickands (Verification.galambos 1 (by norm_num)) unitHalf=3/4 ∧
      (2:ℝ)^((1-(1:ℝ))/1)=1 := by
  constructor
  · rw [galambos_pickands_midpoint]
    norm_num [Real.rpow_neg_one]
  · norm_num

theorem galambos_printed_midpoint_false :
    ¬∀ (δ : ℝ) (hδ : 0<δ),
      Verification.copulaPickands (Verification.galambos δ hδ) unitHalf=(2:ℝ)^((1-δ)/δ) := by
  intro h
  have hh := h 1 (by norm_num)
  rw [galambos_printed_midpoint_counterexample.1,galambos_printed_midpoint_counterexample.2] at hh
  norm_num at hh

end Papers.AnsariRockel2024
