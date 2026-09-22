import Verification.ConditionalLawRealization
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-! # Continuous conditional-law costs for xi and the correlation ratio -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- Squared CDF integral as a continuous cost of two independent samples. -/
theorem integral_unit_cdf_sq (μ : ProbabilityMeasure I) :
    (∫ t : I, μ.toMeasure.real (Iic t) ^ 2) =
      1 - ∫ p : I × I, max (p.1 : ℝ) (p.2 : ℝ) ∂(μ.prod μ).toMeasure := by
  let m := (μ.prod μ).toMeasure.map (fun p : I × I => max p.1 p.2)
  have hm : Measurable (fun p : I × I => max p.1 p.2) := by fun_prop
  have he (t : I) : m.real (Iic t) = μ.toMeasure.real (Iic t) ^ 2 := by
    change ((μ.prod μ).toMeasure.map _ (Iic t)).toReal = _
    rw [Measure.map_apply hm measurableSet_Iic]
    have hs : (fun p : I × I => max p.1 p.2) ⁻¹' Iic t = Iic t ×ˢ Iic t := by
      ext p
      simp only [mem_preimage, mem_Iic, max_le_iff, mem_prod]
    rw [hs]
    change ((μ.toMeasure.prod μ.toMeasure) (Iic t ×ˢ Iic t)).toReal = _
    rw [Measure.prod_prod, ENNReal.toReal_mul]
    exact (pow_two _).symm
  have h := integral_unit_cdf m
  simp_rw [he] at h
  rw [integral_map hm.aemeasurable continuous_subtype_val.aestronglyMeasurable] at h
  exact h

noncomputable def lawXiCost (μ : ProbabilityMeasure I) : ℝ :=
  6 * (1 - ∫ p : I × I, max (p.1 : ℝ) (p.2 : ℝ) ∂(μ.prod μ).toMeasure) - 2

noncomputable def lawEtaCost (μ : ProbabilityMeasure I) : ℝ :=
  12 * ((∫ x : I, (x : ℝ) ∂μ.toMeasure) - 1 / 2) ^ 2

theorem continuous_lawXiCost : Continuous lawXiCost := by
  have hc := ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun p : I × I => max (p.1 : ℝ) (p.2 : ℝ), by fun_prop⟩ : C(I × I, ℝ))
  have hp : Continuous (fun μ : ProbabilityMeasure I => μ.prod μ) :=
    ProbabilityMeasure.continuous_prod.comp (continuous_id.prodMk continuous_id)
  exact (continuous_const.mul (continuous_const.sub (hc.comp hp))).sub continuous_const

theorem continuous_lawEtaCost : Continuous lawEtaCost := by
  have hc := ProbabilityMeasure.continuous_integral_continuousMap
    (⟨fun x : I => (x : ℝ), continuous_subtype_val⟩ : C(I, ℝ))
  exact continuous_const.mul ((hc.sub continuous_const).pow 2)

/-- Xi is a continuous linear statistic of the law of conditional laws. -/
theorem chatterjeeXi_eq_integral_conditionalLaw (C : Copula 2) :
    C.chatterjeeXi = ∫ μ, lawXiCost μ ∂(conditionalLaw C).toMeasure := by
  change C.chatterjeeXi = ∫ μ, lawXiCost μ ∂((volume : Measure I).map _)
  erw [integral_map (measurable_conditionalLawMap C).aemeasurable
    continuous_lawXiCost.aestronglyMeasurable]
  have hi : Integrable (fun p : I × I => C.conditionalCDF p.2 p.1 ^ 2)
      ((volume : Measure I).prod volume) := by
    refine (integrable_const (1 : ℝ)).mono'
      (C.measurable_conditionalCDF.pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [C.conditionalCDF_nonneg p.2 p.1, C.conditionalCDF_le_one p.2 p.1]
  have he (u : I) : lawXiCost ⟨C.conditionalKernel u, inferInstance⟩ =
      6 * (∫ t : I, C.conditionalCDF u t ^ 2) - 2 := by
    unfold lawXiCost
    erw [← integral_unit_cdf_sq]
    rfl
  simp_rw [he]
  rw [integral_sub (hi.integral_prod_right.const_mul 6) (integrable_const (2 : ℝ)),
    integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  unfold Copula.chatterjeeXi
  rw [integral_integral_swap hi]

/-- The correlation ratio is another continuous linear statistic of the same law. -/
theorem correlationRatio_eq_integral_conditionalLaw (C : Copula 2) :
    correlationRatio C = ∫ μ, lawEtaCost μ ∂(conditionalLaw C).toMeasure := by
  change correlationRatio C = ∫ μ, lawEtaCost μ ∂((volume : Measure I).map _)
  erw [integral_map (measurable_conditionalLawMap C).aemeasurable
    continuous_lawEtaCost.aestronglyMeasurable]
  exact (integral_const_mul _ _).symm

end Verification
