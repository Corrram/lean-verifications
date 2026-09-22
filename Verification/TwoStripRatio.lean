import Verification.TwoStrip
import Verification.ConditionalRatioBound

/-! # Conditional means and correlation ratio for two-strip copulas -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem stripKernel_measurable (g : StripDisplacement) :
    Measurable (fun p : I × I => stripKernel g p.1 p.2) := by
  exact (measurable_fst.subtype_val.add (g.continuous.measurable.comp measurable_fst)).ite
    (measurableSet_le measurable_snd measurable_const)
    (measurable_fst.subtype_val.sub (g.continuous.measurable.comp measurable_fst))

theorem conditionalMean_twoStrip (g : StripDisplacement) :
    conditionalMean (twoStrip g) =ᵐ[volume]
      fun u => if u ≤ Copula.unitHalf then 1/2-(∫ v : I, g v) else 1/2+(∫ v : I, g v) := by
  have ha : ∀ᵐ u : I, ∀ᵐ v : I, (twoStrip g).conditionalCDF u v = stripKernel g v u :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v u : I => (twoStrip g).conditionalCDF u v = stripKernel g v u)
      (measurableSet_eq_fun (twoStrip g).measurable_conditionalCDF (stripKernel_measurable g))).mp
      (Filter.Eventually.of_forall (conditionalCDF_twoStrip g))
  have hi : Integrable (fun v : I => (v : ℝ)) := Copula.integrable_continuous_unit volume continuous_subtype_val
  have hg : Integrable g := Copula.integrable_continuous_unit volume g.continuous
  filter_upwards [ha] with u hu
  rw [conditionalMean_eq,integral_congr_ae hu]
  by_cases h : u ≤ Copula.unitHalf
  · simp only [stripKernel,ite_eq_left h]
    rw [integral_add hi hg,Copula.integral_unit_id]
    ring
  · simp only [stripKernel,ite_eq_right h]
    rw [integral_sub hi hg,Copula.integral_unit_id]
    ring

theorem correlationRatio_twoStrip (g : StripDisplacement) :
    correlationRatio (twoStrip g) = 12*(∫ v : I, g v)^2 := by
  have he : (fun u => (conditionalMean (twoStrip g) u-1/2)^2) =ᵐ[volume]
      fun _ => (∫ v : I, g v)^2 := by
    filter_upwards [conditionalMean_twoStrip g] with u hu
    rw [hu]
    split_ifs <;> ring
  rw [correlationRatio,integral_congr_ae he]
  simp

end Verification
