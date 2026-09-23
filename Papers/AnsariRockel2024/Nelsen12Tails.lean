import Copula.TailDependence.Nelsen12

/-! # Nelsen 12 tail coefficients from Table 3 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- Both printed Nelsen 12 tail coefficients for every finite admissible parameter.
The lower expression is algebraically equal to `2 ^ (-1 / θ)`. -/
theorem nelsen12_tails (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen12 θ hθ).HasLowerTailDependence (((2 : ℝ) ^ θ⁻¹)⁻¹) ∧
    (Copula.nelsen12 θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  ⟨Copula.hasLowerTailDependence_nelsen12 θ hθ,
   Copula.hasUpperTailDependence_nelsen12 θ hθ⟩

end Papers.AnsariRockel2024
