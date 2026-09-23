import Copula.TailDependence.Nelsen14

/-! # Nelsen 14 tail coefficients from Table 3 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- Both printed Nelsen 14 tail coefficients for every finite admissible parameter. -/
theorem nelsen14_tails (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen14 θ hθ).HasLowerTailDependence (1 / 2) ∧
    (Copula.nelsen14 θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  ⟨Copula.hasLowerTailDependence_nelsen14 θ hθ,
   Copula.hasUpperTailDependence_nelsen14 θ hθ⟩

end Papers.AnsariRockel2024
