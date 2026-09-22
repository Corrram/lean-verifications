import Copula.Reflection
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Reflecting an actual copula density -/

open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal

namespace Verification

theorem volume_preserving_reflectPoint {d : ℕ} (s : Finset (Fin d)) :
    MeasurePreserving (Copula.reflectPoint s) (volume : Measure (Fin d → I)) volume := by
  classical
  have h (i : Fin d) : MeasurePreserving (fun t : I => if i ∈ s then unitInterval.symm t else t) := by
    by_cases hi : i ∈ s
    · simpa [hi] using unitInterval.measurePreserving_symm
    · simp only [hi, ite_false]
      exact ⟨measurable_id, Measure.map_id⟩
  exact volume_preserving_pi h

theorem reflect_toMeasure_density {d : ℕ} (C : Copula d) (s : Finset (Fin d))
    {f : (Fin d → I) → ℝ≥0∞} (hf : Measurable f)
    (he : C.toMeasure = volume.withDensity f) :
    (C.reflect s).toMeasure = volume.withDensity (fun x => f (Copula.reflectPoint s x)) := by
  rw [Copula.toMeasure_reflect, he]
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (Copula.measurable_reflectPoint s) hA,
    withDensity_apply _ ((Copula.measurable_reflectPoint s) hA), withDensity_apply _ hA]
  have h := (volume_preserving_reflectPoint s).setLIntegral_comp_preimage hA
    (hf.comp (Copula.measurable_reflectPoint s))
  simpa only [Function.comp_apply, Copula.reflectPoint_reflectPoint] using h

end Verification
