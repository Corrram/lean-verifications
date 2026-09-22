import Verification.ConditionalJoin
import Verification.ConditionalMeanRegularity

/-! # Both directional coefficients are affine under a tagged predictor join -/

open MeasureTheory ProbabilityTheory Set Copula.OrdinalSum
open scoped unitInterval

namespace Verification

theorem conditionalJoin_xi (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    (conditionalJoin C D a ha0 ha1).chatterjeeXi =
      (a : ℝ)*C.chatterjeeXi+(1-(a : ℝ))*D.chatterjeeXi := by
  have he (v : I) : (∫ u : I, (conditionalJoin C D a ha0 ha1).conditionalCDF u v^2) =
      (a : ℝ)*(∫ u : I, C.conditionalCDF u v^2)+(1-(a : ℝ))*(∫ u : I, D.conditionalCDF u v^2) := by
    have hj : (fun u => (conditionalJoin C D a ha0 ha1).conditionalCDF u v^2) =ᵐ[volume]
        fun u => unitJoin a (fun t => C.conditionalCDF t v^2) (fun t => D.conditionalCDF t v^2) u := by
      filter_upwards [conditionalJoin_conditionalCDF C D a ha0 ha1 v] with u hu
      rw [hu]
      unfold joinKernel unitJoin
      split_ifs <;> rfl
    rw [integral_congr_ae hj,integral_unitJoin a ha0 ha1 _ _
      ((C.measurable_conditionalCDF_left v).pow_const 2) ((D.measurable_conditionalCDF_left v).pow_const 2)
      (C.integrable_conditionalCDF_sq v) (D.integrable_conditionalCDF_sq v)]
  unfold Copula.chatterjeeXi
  simp_rw [he]
  rw [integral_add (C.integrable_integral_conditionalCDF_sq.const_mul _)
    (D.integrable_integral_conditionalCDF_sq.const_mul _),integral_const_mul,integral_const_mul]
  ring

theorem conditionalMean_conditionalJoin (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    conditionalMean (conditionalJoin C D a ha0 ha1) =ᵐ[volume]
      unitJoin a (conditionalMean C) (conditionalMean D) := by
  have ha : ∀ᵐ u : I, ∀ᵐ v : I,
      (conditionalJoin C D a ha0 ha1).conditionalCDF u v = joinKernel C D a v u :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v u : I => (conditionalJoin C D a ha0 ha1).conditionalCDF u v = joinKernel C D a v u)
      (measurableSet_eq_fun (conditionalJoin C D a ha0 ha1).measurable_conditionalCDF
        (joinKernel_measurable C D a))).mp
      (Filter.Eventually.of_forall (conditionalJoin_conditionalCDF C D a ha0 ha1))
  filter_upwards [ha] with u hu
  rw [conditionalMean_eq,integral_congr_ae hu]
  unfold joinKernel unitJoin
  by_cases h : u ≤ a
  · simp only [ite_eq_left h,conditionalMean_eq]
  · simp only [ite_eq_right h,conditionalMean_eq]

theorem conditionalJoin_correlationRatio (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    correlationRatio (conditionalJoin C D a ha0 ha1) =
      (a : ℝ)*correlationRatio C+(1-(a : ℝ))*correlationRatio D := by
  have he : (fun u => (conditionalMean (conditionalJoin C D a ha0 ha1) u-1/2)^2) =ᵐ[volume]
      unitJoin a (fun u => (conditionalMean C u-1/2)^2) (fun u => (conditionalMean D u-1/2)^2) := by
    filter_upwards [conditionalMean_conditionalJoin C D a ha0 ha1] with u hu
    rw [hu]
    unfold unitJoin
    split_ifs <;> rfl
  rw [correlationRatio,integral_congr_ae he,
    integral_unitJoin a ha0 ha1 (fun u => (conditionalMean C u-1/2)^2) (fun u => (conditionalMean D u-1/2)^2)
      (((conditionalMean_measurable C).sub measurable_const).pow_const 2)
      (((conditionalMean_measurable D).sub measurable_const).pow_const 2)
      (conditionalMean_centered_sq_integrable C) (conditionalMean_centered_sq_integrable D)]
  unfold correlationRatio
  ring

end Verification
