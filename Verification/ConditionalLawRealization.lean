import Verification.ConditionalLawSpace

/-! # Realizing a law of conditional laws by a copula -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- A Markov kernel preserving the uniform law defines a copula. -/
noncomputable def copulaOfKernel (κ : Kernel I I) [IsMarkovKernel κ]
    (hκ : κ ∘ₘ (volume : Measure I) = volume) : Copula 2 :=
  Copula.ofMap ⟨volume ⊗ₘ κ, inferInstance⟩
    (fun p : I × I => ![p.1, p.2]) (by fun_prop) (by
      intro i
      fin_cases i
      · exact Measure.fst_compProd volume κ
      · exact (Measure.snd_compProd volume κ).trans hκ)

/-- Its selected conditional kernel is the original kernel almost everywhere. -/
theorem copulaOfKernel_conditional (κ : Kernel I I) [IsMarkovKernel κ]
    (hκ : κ ∘ₘ (volume : Measure I) = volume) :
    (copulaOfKernel κ hκ).conditionalKernel =ᵐ[volume] κ := by
  let C := copulaOfKernel κ hκ
  have h := condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := C.toMeasure) (X := fun x : Fin 2 → I => x 0)
    (Y := fun x : Fin 2 → I => x 1)
    (measurable_pi_apply 0) (measurable_pi_apply 1) (κ := κ)
  rw [C.map_eval] at h
  apply h
  change ((volume ⊗ₘ κ).map (fun p : I × I => ![p.1, p.2])).map _ = _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map id (volume ⊗ₘ κ) = _
  exact Measure.map_id

/-- Every law of probability measures with uniform barycenter is realized by a copula. -/
theorem exists_copula_conditionalLaw (Λ : ProbabilityMeasure (ProbabilityMeasure I))
    (hΛ : Λ ∈ uniformBarycenter) : ∃ C : Copula 2, conditionalLaw C = Λ := by
  have : Nonempty (ProbabilityMeasure I) := ⟨⟨volume, inferInstance⟩⟩
  obtain ⟨f, hf, hmap⟩ := Λ.toMeasure.exists_measurable_map_eq
  let κ := lawKernel.comap f hf
  have hκ : κ ∘ₘ (volume : Measure I) = volume := by
    rw [← lawKernel_comp_map hf, hmap]
    exact hΛ
  let C := copulaOfKernel κ hκ
  refine ⟨C, ProbabilityMeasure.toMeasure_injective ?_⟩
  change (volume : Measure I).map _ = Λ.toMeasure
  rw [← hmap]
  apply Measure.map_congr
  filter_upwards [copulaOfKernel_conditional κ hκ] with u hu
  exact Subtype.ext hu

end Verification
