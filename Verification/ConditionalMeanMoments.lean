import Verification.ConditionalMeanRegularity

/-! # First moments and affine centered-square moments of conditional means -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem conditionalMean_integrable (C : Copula 2) : Integrable (conditionalMean C) := by
  refine (integrable_const (1 : ℝ)).mono' (conditionalMean_measurable C).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (conditionalMean_mem C u).1]
    exact (conditionalMean_mem C u).2

theorem conditionalMean_integral (C : Copula 2) : (∫ u : I, conditionalMean C u) = 1/2 := by
  have hi : Integrable (fun p : I × I => C.conditionalCDF p.2 p.1)
      ((volume : Measure I).prod volume) := by
    refine (integrable_const (1 : ℝ)).mono' C.measurable_conditionalCDF.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (C.conditionalCDF_nonneg _ _)]
      exact C.conditionalCDF_le_one _ _
  have hm : (∫ u : I, ∫ v : I, C.conditionalCDF u v) = 1/2 := by
    rw [← integral_integral_swap hi]
    simp_rw [C.integral_conditionalCDF]
    exact Copula.integral_unit_id
  simp_rw [conditionalMean_eq]
  rw [integral_sub (integrable_const (1 : ℝ)) hi.integral_prod_right,hm]
  norm_num

theorem conditionalMean_centered_integral (C : Copula 2) :
    (∫ u : I, conditionalMean C u-1/2) = 0 := by
  rw [integral_sub (conditionalMean_integrable C) (integrable_const (1/2 : ℝ)),conditionalMean_integral]
  norm_num

theorem conditionalMean_affine_square_integrable (C : Copula 2) (r s : ℝ) :
    Integrable (fun u => (r*(conditionalMean C u-1/2)+s)^2) := by
  have he (u : I) : (r*(conditionalMean C u-1/2)+s)^2 =
      r^2*(conditionalMean C u-1/2)^2+(2*r*s)*(conditionalMean C u-1/2)+s^2 := by ring
  simp_rw [he]
  exact (((conditionalMean_centered_sq_integrable C).const_mul _).add
    (((conditionalMean_integrable C).sub (integrable_const _)).const_mul _)).add (integrable_const _)

theorem conditionalMean_affine_square_integral (C : Copula 2) (r s : ℝ) :
    (∫ u : I, (r*(conditionalMean C u-1/2)+s)^2) =
      r^2*(∫ u : I, (conditionalMean C u-1/2)^2)+s^2 := by
  have he (u : I) : (r*(conditionalMean C u-1/2)+s)^2 =
      r^2*(conditionalMean C u-1/2)^2+(2*r*s)*(conditionalMean C u-1/2)+s^2 := by ring
  simp_rw [he]
  have hi := (conditionalMean_centered_sq_integrable C).const_mul (r^2)
  have hj := ((conditionalMean_integrable C).sub (integrable_const (1/2 : ℝ))).const_mul (2*r*s)
  have h1 := integral_add (hi.add hj) (integrable_const (s^2))
  have h2 := integral_add hi hj
  dsimp only [Pi.add_apply,Pi.sub_apply] at h1 h2
  rw [h1,h2,integral_const_mul,integral_const_mul,conditionalMean_centered_integral]
  simp

end Verification
