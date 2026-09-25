import Verification.StudentBivariate

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem cdf_map_neg_of_atomless (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (x : ℝ) : ProbabilityTheory.cdf (μ.map (fun z : ℝ => -z)) (-x)=
      1-ProbabilityTheory.cdf μ x := by
  have hs : (fun z : ℝ => -z) ⁻¹' Iic (-x)=Ici x := by ext z; simp
  have he : μ.real (Ici x)=μ.real (Ioi x) := by
    apply measureReal_congr
    filter_upwards [Measure.ae_ne μ x] with z hz
    apply propext
    simp only [mem_Ici,mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm hz),fun h => h.le⟩
  rw [ProbabilityTheory.cdf_eq_real,ProbabilityTheory.cdf_eq_real,
    map_measureReal_apply (by fun_prop) measurableSet_Iic,hs,he,← compl_Iic,
    measureReal_compl measurableSet_Iic,probReal_univ]

theorem ofContinuousMarginals_countermonotonic_of_ae_neg (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i)))
    [NullSingletonClass (marginal μ 0)]
    (he : ∀ᵐ x ∂μ.toMeasure, x 1= -x 0) : ofContinuousMarginals μ hc=countermonotonic := by
  have hm : marginal μ 1=(marginal μ 0).map (fun x : ℝ => -x) := by
    simp only [marginal]
    rw [Measure.map_map (show Measurable (fun x : ℝ => -x) by fun_prop) (measurable_pi_apply (0 : Fin 2))]
    exact Measure.map_congr he
  apply (eq_countermonotonic_iff_ae_eval_eq_symm _).mpr
  change ∀ᵐ x ∂μ.toMeasure.map (marginalTransform μ),x 1=unitInterval.symm (x 0)
  apply (ae_map_iff (measurable_marginalTransform μ).aemeasurable
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
  filter_upwards [he] with x hx
  apply Subtype.ext
  change ProbabilityTheory.cdf (marginal μ 1) (x 1)=1-ProbabilityTheory.cdf (marginal μ 0) (x 0)
  rw [hm,hx,cdf_map_neg_of_atomless]

theorem gaussian_negative_one_ae_neg :
    ∀ᵐ x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation (-1)),x 1= -x 0 := by
  rw [← map_gaussianMix (r := -1) (by norm_num)]
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
  exact Filter.Eventually.of_forall fun x => by simp [gaussianMix]

theorem gaussianScaleMixture_negative_one (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    gaussianScaleMixture (bivariateCorrelation (-1)) (bivariateCorrelation_posSemidef (by norm_num))
      (by intro i; fin_cases i <;> rfl) μ s hs hp=countermonotonic := by
  let : NullSingletonClass (marginal (gaussianScaleMixtureLaw (bivariateCorrelation (-1)) μ s) 0) :=
    atomless_gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef (by norm_num))
      (by intro i; fin_cases i <;> rfl) μ s hs hp 0
  apply ofContinuousMarginals_countermonotonic_of_ae_neg
  change ∀ᵐ x ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation (-1))).prod
    μ.toMeasure).map (fun p i => s p.2*p.1 i),x 1= -x 0
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
  filter_upwards [gaussian_negative_one_ae_neg] with x hx
  exact Filter.Eventually.of_forall fun t => by change s t*x 1= -(s t*x 0); rw [hx,mul_neg]

theorem studentBivariate_negative_one (ν : ℝ) (hν : 0<ν) :
    studentBivariate (-1) (by norm_num) ν hν=countermonotonic :=
  gaussianScaleMixture_negative_one _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

end Verification
