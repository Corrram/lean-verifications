import Verification.ScaleMixtureCDF
import Verification.GaussianOrder
import Verification.SklarOrder

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussianBivariate_cdf_normal_rectangle {r : ℝ} (hr : r∈Icc (-1) 1) (a b : ℝ) :
    (gaussianBivariate r hr).cdf ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b]=
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).real
        {x | x 0≤a ∧ x 1≤b} := by
  rw [Copula.cdf]
  change ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).map
    (fun x i => cdfUnit (gaussianReal 0 1) (x i))).real (Iic _)=_
  rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext x
  change (∀ i : Fin 2,cdfUnit (gaussianReal 0 1) (x i)≤
    ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b] i) ↔ _
  simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  change (ProbabilityTheory.cdf (gaussianReal 0 1) (x 0)≤ProbabilityTheory.cdf (gaussianReal 0 1) a ∧
    ProbabilityTheory.cdf (gaussianReal 0 1) (x 1)≤ProbabilityTheory.cdf (gaussianReal 0 1) b) ↔ _
  simp only [standardNormalCDF_strictMono.le_iff_le,Set.mem_ofPred_eq]

theorem gaussianScaleMixtureLaw_rectangle {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (a b : ℝ) :
    (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure.real (Iic ![a,b])=
      ∫ t, (gaussianBivariate r hr).cdf
        ![cdfUnit (gaussianReal 0 1) (a/s t),cdfUnit (gaussianReal 0 1) (b/s t)] ∂μ.toMeasure := by
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let A := {p : EuclideanSpace ℝ (Fin 2) × ℝ | s p.2*p.1 0≤a ∧ s p.2*p.1 1≤b}
  have hA : MeasurableSet A := by
    apply MeasurableSet.inter
    · exact measurableSet_le (show Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => s p.2*p.1 0) by fun_prop) measurable_const
    · exact measurableSet_le (show Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => s p.2*p.1 1) by fun_prop) measurable_const
  have hm : Measurable (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => fun i => s p.2*p.1 i) := by fun_prop
  change ((G.prod μ.toMeasure).map (fun p i => s p.2*p.1 i)).real (Iic ![a,b])=_
  rw [map_measureReal_apply hm measurableSet_Iic]
  have he : (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => fun i => s p.2*p.1 i) ⁻¹' Iic ![a,b]=A := by
    ext p
    simp [A,Pi.le_def,Fin.forall_fin_two]
  rw [he,← integral_indicator_one hA]
  have hi : Integrable (A.indicator (fun _ => (1:ℝ))) (G.prod μ.toMeasure) :=
    (integrable_const _).indicator hA
  change (∫ p, A.indicator (fun _ => (1:ℝ)) p ∂G.prod μ.toMeasure)=_
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hp] with t ht
  rw [gaussianBivariate_cdf_normal_rectangle hr]
  have hB : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | x 0≤a/s t ∧ x 1≤b/s t} :=
    (measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop) measurable_const).inter
      (measurableSet_le (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 1) by fun_prop) measurable_const)
  rw [← integral_indicator_one hB]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [A,indicator,mem_ofPred_eq,le_div_iff₀ ht]
    simp only [mul_comm (s t),Pi.one_apply]

theorem gaussianScaleMixtureLaw_lowerOrthant {r q : ℝ} (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1)
    (hrq : r≤q) (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (x : Fin 2 → ℝ) :
    (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure.real (Iic x)≤
      (gaussianScaleMixtureLaw (bivariateCorrelation q) μ s).toMeasure.real (Iic x) := by
  have hx : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx,gaussianScaleMixtureLaw_rectangle hr μ s hs hp,gaussianScaleMixtureLaw_rectangle hq μ s hs hp]
  have hi (C : Copula 2) : Integrable (fun t => C.cdf
      ![cdfUnit (gaussianReal 0 1) (x 0/s t),cdfUnit (gaussianReal 0 1) (x 1/s t)]) μ.toMeasure := by
    have hm : Measurable (fun t => C.cdf
        ![cdfUnit (gaussianReal 0 1) (x 0/s t),cdfUnit (gaussianReal 0 1) (x 1/s t)]) :=
      C.continuous_cdf.measurable.comp (by fun_prop)
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (C.cdf_nonneg _)]
      exact C.cdf_le_one _
  apply integral_mono (hi _) (hi _)
  intro t
  exact gaussianBivariate_lowerOrthant_monotone hr hq hrq _

theorem gaussianScaleMixture_lowerOrthant {r q : ℝ} (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1)
    (hrq : r≤q) (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).LowerOrthantLE
    (gaussianScaleMixture (bivariateCorrelation q) (bivariateCorrelation_posSemidef hq)
      (by intro i; fin_cases i <;> rfl) μ s hs hp) := by
  apply sklar_lowerOrthant_of_common_marginals
    (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s)
    (gaussianScaleMixtureLaw (bivariateCorrelation q) μ s)
  · exact continuous_gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp
  · intro i
    rw [gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
      (by intro j; fin_cases j <;> rfl) μ s hs,
      gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hq)
      (by intro j; fin_cases j <;> rfl) μ s hs]
  · exact isSklarCopula_gaussianScaleMixture _ _ _ _ _ _ _
  · exact isSklarCopula_gaussianScaleMixture _ _ _ _ _ _ _
  · exact gaussianScaleMixtureLaw_lowerOrthant hr hq hrq μ s hs hp

end Verification
