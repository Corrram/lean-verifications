import Verification.GaussianScaledDensity
import Verification.ScaleMixtureDensity

open ProbabilityTheory MeasureTheory Set Copula
open scoped ENNReal

namespace Verification

noncomputable def gaussianScaleMixtureJointDensity (r : ℝ) (μ : ProbabilityMeasure ℝ)
    (s : ℝ → ℝ) (p : ℝ×ℝ) : ℝ≥0∞ :=
  ∫⁻ t, gaussianPDF 0 (NNReal.mk ((s t)^2) (sq_nonneg _)) p.1*
    gaussianPDF (r*p.1) (NNReal.mk ((s t*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2 ∂μ.toMeasure

theorem measurable_gaussianScaleMixtureJointDensity (r : ℝ) (μ : ProbabilityMeasure ℝ)
    (s : ℝ → ℝ) (hs : Measurable s) : Measurable (gaussianScaleMixtureJointDensity r μ s) := by
  apply Measurable.lintegral_prod_right
  unfold gaussianPDF gaussianPDFReal
  fun_prop

theorem gaussianScaleMixtureLaw_joint_withDensity {r : ℝ} (hr : r∈Ioo (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure.map MeasurableEquiv.finTwoArrow=
      (volume : Measure (ℝ×ℝ)).withDensity (gaussianScaleMixtureJointDensity r μ s) := by
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let D := fun t : ℝ => fun p : ℝ×ℝ =>
    gaussianPDF 0 (NNReal.mk ((s t)^2) (sq_nonneg _)) p.1*
      gaussianPDF (r*p.1) (NNReal.mk ((s t*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2
  have hD : Measurable (Function.uncurry D) := by
    unfold D Function.uncurry gaussianPDF gaussianPDFReal
    fun_prop
  change ((G.prod μ.toMeasure).map (fun p i => s p.2*p.1 i)).map MeasurableEquiv.finTwoArrow=_
  rw [Measure.map_map MeasurableEquiv.finTwoArrow.measurable (by fun_prop)]
  apply Measure.ext_of_lintegral
  intro f hf
  have hfm : Measurable (fun p : EuclideanSpace ℝ (Fin 2)×ℝ => f (s p.2*p.1 0,s p.2*p.1 1)) := hf.comp (by fun_prop)
  rw [lintegral_map hf (by fun_prop)]
  change (∫⁻ p, f (s p.2*p.1 0,s p.2*p.1 1) ∂G.prod μ.toMeasure)=_
  rw [lintegral_prod_symm _ hfm.aemeasurable]
  have he : (fun t => ∫⁻ x, f (s t*x 0,s t*x 1) ∂G)=ᵐ[μ.toMeasure]
      fun t => ∫⁻ p, D t p*f p := by
    filter_upwards [hp] with t ht
    rw [← lintegral_map hf (by fun_prop),gaussian_scaled_pair_density hr (s t) ht.ne']
    exact lintegral_withDensity_eq_lintegral_mul _ (by
      unfold gaussianPDF gaussianPDFReal
      fun_prop) hf
  rw [lintegral_congr_ae he,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianScaleMixtureJointDensity r μ s hs) hf]
  rw [lintegral_lintegral_swap (hD.mul (hf.comp measurable_snd)).aemeasurable]
  apply lintegral_congr
  intro p
  change (∫⁻ t, D t p*f p ∂μ.toMeasure)=_
  rw [lintegral_mul_const _ (by
    unfold D gaussianPDF gaussianPDFReal
    fun_prop)]
  rfl

theorem gaussianScaleMixtureJointDensity_pos {r : ℝ} (hr : r∈Ioo (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (p : ℝ×ℝ) :
    0<gaussianScaleMixtureJointDensity r μ s p := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm : Measurable (fun t => gaussianPDF 0 (NNReal.mk ((s t)^2) (sq_nonneg _)) p.1*
      gaussianPDF (r*p.1) (NNReal.mk ((s t*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  have he := (lintegral_eq_zero_iff hm).mp hz
  obtain ⟨t,ht,hzero⟩ := (hp.and he).exists
  have hv (a : ℝ) (ha : a≠0) : (NNReal.mk (a^2) (sq_nonneg a))≠0 := by
    intro h
    have h' : a^2=0 := congrArg (fun v : NNReal => (v:ℝ)) h
    exact ha (sq_eq_zero_iff.mp h')
  have hroot : Real.sqrt (1-r^2)≠0 := Real.sqrt_ne_zero'.mpr (by nlinarith [hr.1,hr.2])
  have hn := mul_ne_zero (gaussianPDF_pos 0 (hv (s t) ht.ne') p.1).ne'
    (gaussianPDF_pos (r*p.1) (hv (s t*Real.sqrt (1-r^2)) (mul_ne_zero ht.ne' hroot)) p.2).ne'
  exact hn hzero

theorem gaussianScaleMixtureLaw_joint_equivalent_volume {r : ℝ} (hr : r∈Ioo (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure.map MeasurableEquiv.finTwoArrow ≪ volume ∧
      volume ≪ (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure.map MeasurableEquiv.finTwoArrow := by
  rw [gaussianScaleMixtureLaw_joint_withDensity hr μ s hs hp]
  refine ⟨withDensity_absolutelyContinuous _ _,?_⟩
  exact withDensity_absolutelyContinuous'
    (measurable_gaussianScaleMixtureJointDensity r μ s hs).aemeasurable
    (Filter.Eventually.of_forall fun p => (gaussianScaleMixtureJointDensity_pos hr μ s hs hp p).ne')

end Verification
