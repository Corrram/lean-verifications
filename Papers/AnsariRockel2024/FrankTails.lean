import Verification.FrankTails
import Copula.TailDependence.Examples

/-! # Table 3: both Frank tail coefficients, for every finite parameter -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

theorem frank_positive_tails (θ : ℝ) (hθ : 0 < θ) :
    (Copula.frank θ hθ).HasLowerTailDependence 0 ∧
      (Copula.frank θ hθ).HasUpperTailDependence 0 :=
  Verification.frank_positive_tails θ hθ

theorem frank_negative_tails (θ : ℝ) (hθ : θ < 0) :
    (Copula.frankNegative θ hθ).HasLowerTailDependence 0 ∧
      (Copula.frankNegative θ hθ).HasUpperTailDependence 0 :=
  Verification.frank_negative_tails θ hθ

theorem frank_zero_tails :
    (Copula.independence 2).HasLowerTailDependence 0 ∧
      (Copula.independence 2).HasUpperTailDependence 0 :=
  ⟨Copula.hasLowerTailDependence_independence, Copula.hasUpperTailDependence_independence⟩

end Papers.AnsariRockel2024
