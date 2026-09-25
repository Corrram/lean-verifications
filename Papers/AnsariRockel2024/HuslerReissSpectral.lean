import Verification.HuslerReissConstruction

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem huslerReiss_spectral_isExtremeValue (δ : ℝ) (hδ : 0<δ) :
    (Verification.huslerReissPositive δ hδ).IsExtremeValue :=
  Verification.huslerReissPositive_isExtremeValue δ hδ

theorem huslerReiss_spectral_isCI (δ : ℝ) (hδ : 0<δ) :
    (Verification.huslerReissPositive δ hδ).IsCI :=
  Verification.huslerReissPositive_isCI δ hδ

theorem huslerReiss_pickands_spectral (δ : ℝ) (hδ : 0<δ) (t : I) :
    Verification.copulaPickands (Verification.huslerReissPositive δ hδ) t=
      ∫ z,max ((1-(t:ℝ))*Real.exp ((2/δ)*z-(2/δ)^2/2)) (t:ℝ) ∂gaussianReal 0 1 :=
  Verification.huslerReissPositive_pickands_spectral δ hδ t

end Papers.AnsariRockel2024
