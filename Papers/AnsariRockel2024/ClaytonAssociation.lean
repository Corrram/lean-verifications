import Papers.AnsariRockel2024.ClaytonResults
import Verification.ClaytonTau

/-! # Table 6: positive-Clayton Kendall tau -/

open ProbabilityTheory MeasureTheory Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem clayton_positive_conditionalCDF {θ : ℝ} (hθ : 0<θ) (v : I) (hv : 0<(v:ℝ)) :
    (fun u => (clayton 2 θ hθ).conditionalCDF u v) =ᵐ[volume]
      fun u => Verification.claytonPartial θ u v := Verification.clayton_conditionalCDF hθ v hv

theorem clayton_positive_kendallTau {θ : ℝ} (hθ : 0<θ) :
    (clayton 2 θ hθ).kendallTau=θ/(θ+2) := Verification.clayton_kendallTau hθ

theorem clayton_zero_kendallTau : (independence 2).kendallTau=0 := by simp

theorem clayton_negative_one_kendallTau :
    (claytonNegative (-1) (by norm_num) (by norm_num)).kendallTau= -1 := by
  rw [clayton_negative_one]
  simp

end Papers.AnsariRockel2024
