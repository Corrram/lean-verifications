import Verification.ProbabilityUnitBorel
import Verification.ConditionalMean
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Laws of conditional distributions with a uniform barycenter -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- Evaluation turns a probability law into a Markov kernel. -/
def lawKernel : Kernel (ProbabilityMeasure I) I where
  toFun := ProbabilityMeasure.toMeasure
  measurable' := measurable_subtype_coe

instance : IsMarkovKernel lawKernel := ⟨fun μ => μ.prop⟩

/-- Laws of conditional laws whose averaged response distribution is uniform. -/
def uniformBarycenter : Set (ProbabilityMeasure (ProbabilityMeasure I)) :=
  {Λ | lawKernel ∘ₘ Λ.toMeasure = volume}

private theorem integral_lawKernel (Λ : ProbabilityMeasure (ProbabilityMeasure I))
    (f : C(I, ℝ)) :
    (∫ x, f x ∂(lawKernel ∘ₘ Λ.toMeasure)) =
      ∫ μ, ∫ x, f x ∂μ.toMeasure ∂Λ.toMeasure := by
  rw [Measure.comp_eq_comp_const_apply]
  exact Kernel.integral_comp
    (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem uniformBarycenter_iff (Λ : ProbabilityMeasure (ProbabilityMeasure I)) :
    Λ ∈ uniformBarycenter ↔ ∀ f : C(I, ℝ),
      (∫ μ, ∫ x, f x ∂μ.toMeasure ∂Λ.toMeasure) = ∫ x, f x := by
  constructor
  · intro h f
    rw [← integral_lawKernel, h]
  · intro h
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    change (∫ x, f.toContinuousMap x ∂(lawKernel ∘ₘ Λ.toMeasure)) = _
    rw [integral_lawKernel Λ f.toContinuousMap]
    exact h f.toContinuousMap

/-- Admissible laws form a compact set in the weak topology on laws of laws. -/
theorem isCompact_uniformBarycenter : IsCompact uniformBarycenter := by
  have he : uniformBarycenter = ⋂ f : C(I, ℝ),
      {Λ : ProbabilityMeasure (ProbabilityMeasure I) |
        (∫ μ, ∫ x, f x ∂μ.toMeasure ∂Λ.toMeasure) = ∫ x, f x} := by
    ext Λ
    simp only [mem_iInter, mem_ofPred_eq, uniformBarycenter_iff]
  rw [he]
  apply IsClosed.isCompact
  apply isClosed_iInter
  intro f
  exact isClosed_eq
    (ProbabilityMeasure.continuous_integral_continuousMap
      (⟨_, ProbabilityMeasure.continuous_integral_continuousMap f⟩ : C(ProbabilityMeasure I, ℝ)))
    continuous_const

/-- The distribution, under the uniform conditioning variable, of the conditional law. -/
noncomputable def conditionalLaw (C : Copula 2) : ProbabilityMeasure (ProbabilityMeasure I) :=
  ProbabilityMeasure.map (⟨volume, inferInstance⟩ : ProbabilityMeasure I)
    (fun u => ⟨C.conditionalKernel u, inferInstance⟩)

theorem measurable_conditionalLawMap (C : Copula 2) :
    Measurable (fun u => (⟨C.conditionalKernel u, inferInstance⟩ : ProbabilityMeasure I)) :=
  C.conditionalKernel.measurable.subtype_mk

/-- Composition with evaluation commutes with the law of a random probability measure. -/
theorem lawKernel_comp_map {f : I → ProbabilityMeasure I} (hf : Measurable f) :
    lawKernel ∘ₘ ((volume : Measure I).map f) =
      (lawKernel.comap f hf) ∘ₘ volume := by
  ext s hs
  rw [Measure.bind_apply hs lawKernel.aemeasurable,
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (lawKernel.measurable_coe hs) hf]
  rfl

theorem conditionalLaw_mem_uniformBarycenter (C : Copula 2) :
    conditionalLaw C ∈ uniformBarycenter := by
  change lawKernel ∘ₘ ((volume : Measure I).map _) = volume
  rw [lawKernel_comp_map (measurable_conditionalLawMap C)]
  exact C.conditionalKernel_comp_volume

end Verification
