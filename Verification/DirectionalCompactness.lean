import Verification.ConditionalLawCosts

/-! # Compactness of the full attainable xi--eta region -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- The full directional coefficient region, including all singular copulas, is compact. -/
theorem isCompact_xi_eta_region :
    IsCompact (Set.range (fun C : Copula 2 => (C.chatterjeeXi, correlationRatio C))) := by
  let F : ProbabilityMeasure (ProbabilityMeasure I) → ℝ × ℝ := fun Λ =>
    (∫ μ, lawXiCost μ ∂Λ.toMeasure, ∫ μ, lawEtaCost μ ∂Λ.toMeasure)
  have hc : Continuous F :=
    (ProbabilityMeasure.continuous_integral_continuousMap
      (⟨lawXiCost, continuous_lawXiCost⟩ : C(ProbabilityMeasure I, ℝ))).prodMk
    (ProbabilityMeasure.continuous_integral_continuousMap
      (⟨lawEtaCost, continuous_lawEtaCost⟩ : C(ProbabilityMeasure I, ℝ)))
  have he : Set.range (fun C : Copula 2 => (C.chatterjeeXi, correlationRatio C)) =
      F '' uniformBarycenter := by
    ext p
    constructor
    · rintro ⟨C, rfl⟩
      refine ⟨conditionalLaw C, conditionalLaw_mem_uniformBarycenter C, ?_⟩
      exact Prod.ext (chatterjeeXi_eq_integral_conditionalLaw C).symm
        (correlationRatio_eq_integral_conditionalLaw C).symm
    · rintro ⟨Λ, hΛ, rfl⟩
      obtain ⟨C, rfl⟩ := exists_copula_conditionalLaw Λ hΛ
      exact ⟨C, Prod.ext (chatterjeeXi_eq_integral_conditionalLaw C)
        (correlationRatio_eq_integral_conditionalLaw C)⟩
  rw [he]
  exact isCompact_uniformBarycenter.image hc

end Verification
