import Verification.HuslerReissParameter
import Papers.AnsariRockel2024.HuslerReissTails
import Papers.AnsariRockel2024.ExtremeValueOrders

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem huslerReiss_pickands_antitone (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) (hδε : δ≤ε)
    (t : I) (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    Verification.copulaPickands (Verification.huslerReissPositive ε hε) t ≤
      Verification.copulaPickands (Verification.huslerReissPositive δ hδ) t := by
  rw [huslerReiss_pickands_interior ε hε t ht,huslerReiss_pickands_interior δ hδ t ht]
  exact Verification.huslerReissExponent_antitone _ _ (by linarith [ht.2]) ht.1 hδ hε hδε

theorem huslerReiss_lowerOrthant_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) (hδε : δ≤ε) :
    (Verification.huslerReissPositive δ hδ).LowerOrthantLE (Verification.huslerReissPositive ε hε) := by
  apply (extremeValue_pickands_order _ _ (Verification.huslerReissPositive_isExtremeValue δ hδ)
    (Verification.huslerReissPositive_isExtremeValue ε hε)).mpr
  intro t ht0 ht1
  exact huslerReiss_pickands_antitone δ ε hδ hε hδε t ⟨ht0,ht1⟩

theorem huslerReiss_schurBoth_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) (hδε : δ≤ε) :
    (Verification.huslerReissPositive δ hδ).SchurBothLE (Verification.huslerReissPositive ε hε) := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (Verification.huslerReissPositive_isExtremeValue δ hδ)
    (Verification.huslerReissPositive_isExtremeValue ε hε) (Verification.huslerReissPositive_isCI δ hδ)
    (Verification.huslerReissPositive_isCI ε hε)).mpr
  intro t ht0 ht1
  exact huslerReiss_pickands_antitone δ ε hδ hε hδε t ⟨ht0,ht1⟩

theorem huslerReiss_lowerOrthant_iff (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    (Verification.huslerReissPositive δ hδ).LowerOrthantLE (Verification.huslerReissPositive ε hε) ↔ δ≤ε := by
  constructor
  · intro h
    have hh := h.upperTailDependence_le (huslerReiss_tails δ hδ).2 (huslerReiss_tails ε hε).2
    have hc : ProbabilityTheory.cdf (gaussianReal 0 1) (1/ε)≤ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ) := by linarith
    have hi := Verification.standardNormalCDF_strictMono.le_iff_le.mp hc
    have hm := (div_le_div_iff₀ hε hδ).mp hi
    linarith
  · exact huslerReiss_lowerOrthant_mono δ ε hδ hε

theorem huslerReiss_schurBoth_iff (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    (Verification.huslerReissPositive δ hδ).SchurBothLE (Verification.huslerReissPositive ε hε) ↔ δ≤ε := by
  constructor
  · intro h
    apply (huslerReiss_lowerOrthant_iff δ ε hδ hε).mp
    exact (cis_schur_iff_orthant _ _ (Verification.huslerReissPositive_isCI δ hδ).1
      (Verification.huslerReissPositive_isCI ε hε).1).mp h.1
  · exact huslerReiss_schurBoth_mono δ ε hδ hε

end Papers.AnsariRockel2024
