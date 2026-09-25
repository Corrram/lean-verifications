import Papers.AnsariRockel2024.FrankContinuity
import Verification.FrankTau

/-! # Table 6: Frank Kendall tau and the first Debye function -/

open ProbabilityTheory MeasureTheory Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem frank_conditionalCDF {θ : ℝ} (hθ : θ≠0) (v : I) :
    (fun u => (frankSigned θ).conditionalCDF u v) =ᵐ[volume]
      fun u => Verification.frankPartial θ u v := by
  apply Verification.frank_conditionalCDF_of_cdf _ hθ
  intro u v
  rw [frankSigned_cdf_regular,Verification.frankRegularCDF_eq_real hθ]

theorem frank_kendallTau {θ : ℝ} (hθ : θ≠0) :
    (frankSigned θ).kendallTau=1-4/θ*(1-Verification.debyeOne θ) := by
  apply Verification.frank_kendallTau_of_cdf _ hθ
  intro u v
  rw [frankSigned_cdf_regular,Verification.frankRegularCDF_eq_real hθ]

theorem frank_kendallTau_zero : (frankSigned 0).kendallTau=0 := by
  simp [frankSigned]

end Papers.AnsariRockel2024
