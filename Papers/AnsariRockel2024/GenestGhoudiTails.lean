import Copula.TailDependence.GenestGhoudi

/-! # Genest–Ghoudi tail coefficients from Table 3 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- Both printed Genest–Ghoudi tail coefficients for every finite admissible parameter. -/
theorem genestGhoudi_tails (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.genestGhoudi θ hθ).HasLowerTailDependence 0 ∧
    (Copula.genestGhoudi θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  ⟨Copula.hasLowerTailDependence_genestGhoudi θ hθ,
   Copula.hasUpperTailDependence_genestGhoudi θ hθ⟩

end Papers.AnsariRockel2024
