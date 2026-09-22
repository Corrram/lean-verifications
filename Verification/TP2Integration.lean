import Copula.Dependence.TotalPositivity
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace Verification

/-- Integrating a pointwise cross-product inequality preserves its determinant sign. -/
theorem lintegral_cross_le {f g : I → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (μ ν : Measure I)
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f x*g y ≤ g x*f y) :
    (∫⁻ x, f x ∂μ)*(∫⁻ y, g y ∂ν) ≤ (∫⁻ x, g x ∂μ)*(∫⁻ y, f y ∂ν) := by
  rw [← lintegral_lintegral_mul hf.aemeasurable hg.aemeasurable,
    ← lintegral_lintegral_mul hg.aemeasurable hf.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [h] with x hx
  exact lintegral_mono_ae hx

/-- Integration over ordered rectangles preserves TP2, without section-integrability assumptions. -/
theorem tp2_rectangle_integrals (f : I → I → ℝ≥0∞)
    (hf : Measurable (fun p : I × I => f p.1 p.2))
    (S T U V : Set I) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (h : ∀ a ∈ S, ∀ b ∈ T, ∀ u ∈ U, ∀ v ∈ V, f b u*f a v ≤ f a u*f b v) :
    (∫⁻ a in S, ∫⁻ v in V, f a v)*(∫⁻ b in T, ∫⁻ u in U, f b u) ≤
      (∫⁻ a in S, ∫⁻ u in U, f a u)*(∫⁻ b in T, ∫⁻ v in V, f b v) := by
  apply lintegral_cross_le
    (hf.lintegral_prod_right' (ν := volume.restrict V))
    (hf.lintegral_prod_right' (ν := volume.restrict U))
  filter_upwards [ae_restrict_mem hS] with a ha
  filter_upwards [ae_restrict_mem hT] with b hb
  have he := lintegral_cross_le
    (hf.comp (measurable_const.prodMk measurable_id) : Measurable (f b))
    (hf.comp (measurable_const.prodMk measurable_id) : Measurable (f a))
    (volume.restrict U) (volume.restrict V) (by
      filter_upwards [ae_restrict_mem hU] with u hu
      filter_upwards [ae_restrict_mem hV] with v hv
      exact h a ha b hb u hu v hv)
  simpa only [Function.comp_def,id_eq,mul_comm] using he

end Verification
