import Verification.ConditionalRatioBound
import Copula.Rank.ChatterjeeMixture

/-! # Conditional means under copula mixtures -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem response_cdf_integrable (C : Copula 2) (t : I) :
    Integrable (fun v : I => C.conditionalCDF t v) := by
  have h := (centered_section C t).1.add (Copula.integrable_continuous_unit volume continuous_subtype_val)
  change Integrable (fun v : I => C.conditionalCDF t v-(v : ℝ)+(v : ℝ)) at h
  simpa only [sub_add_cancel] using h

theorem conditionalMean_mix (C D : Copula 2) (a : I) :
    conditionalMean (C.mix D a) =ᵐ[volume]
      fun t => (a : ℝ)*conditionalMean C t+(1-(a : ℝ))*conditionalMean D t := by
  have hm : Measurable (fun p : I × I => (a : ℝ)*C.conditionalCDF p.2 p.1+
      (1-(a : ℝ))*D.conditionalCDF p.2 p.1) :=
    (measurable_const.mul C.measurable_conditionalCDF).add (measurable_const.mul D.measurable_conditionalCDF)
  have ha : ∀ᵐ t : I, ∀ᵐ v : I, (C.mix D a).conditionalCDF t v =
      (a : ℝ)*C.conditionalCDF t v+(1-(a : ℝ))*D.conditionalCDF t v :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v t : I => (C.mix D a).conditionalCDF t v = (a : ℝ)*C.conditionalCDF t v+(1-(a : ℝ))*D.conditionalCDF t v)
      (measurableSet_eq_fun (C.mix D a).measurable_conditionalCDF hm)).mp
      (Filter.Eventually.of_forall (Copula.conditionalCDF_mix C D a))
  filter_upwards [ha] with t ht
  rw [conditionalMean_eq, integral_congr_ae ht,
    integral_add ((response_cdf_integrable C t).const_mul _) ((response_cdf_integrable D t).const_mul _),
    integral_const_mul, integral_const_mul, conditionalMean_eq, conditionalMean_eq]
  ring

theorem conditionalMean_independence :
    conditionalMean (Copula.independence 2) =ᵐ[volume] fun _ => (1/2 : ℝ) := by
  filter_upwards [Copula.conditionalKernel_independence] with t ht
  unfold conditionalMean
  rw [ht]
  exact Copula.integral_unit_id

theorem correlationRatio_mix_independence (C : Copula 2) (a : I) :
    correlationRatio (C.mix (Copula.independence 2) a) = (a : ℝ)^2*correlationRatio C := by
  unfold correlationRatio
  have he : (fun t => (conditionalMean (C.mix (Copula.independence 2) a) t-1/2)^2) =ᵐ[volume]
      fun t => (a : ℝ)^2*(conditionalMean C t-1/2)^2 := by
    filter_upwards [conditionalMean_mix C (Copula.independence 2) a, conditionalMean_independence] with t ht hi
    rw [ht,hi]
    ring
  rw [integral_congr_ae he, integral_const_mul]
  ring

end Verification
