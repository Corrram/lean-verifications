import Verification.ScaleMixtureCDF
import Verification.GaussianNormalDensity

open ProbabilityTheory MeasureTheory Set
open scoped ENNReal

namespace Verification

noncomputable def normalScaleMixtureDensity (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, gaussianPDF 0 (NNReal.mk ((s t)^2) (sq_nonneg _)) x ∂μ.toMeasure

theorem measurable_normalScaleMixtureDensity (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) : Measurable (normalScaleMixtureDensity μ s) := by
  apply Measurable.lintegral_prod_right
  unfold gaussianPDF gaussianPDFReal
  fun_prop

theorem normalScaleMixtureMarginal_withDensity (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    normalScaleMixtureMarginal μ s=volume.withDensity (normalScaleMixtureDensity μ s) := by
  have hD : Measurable (fun p : ℝ×ℝ => gaussianPDF 0 (NNReal.mk ((s p.1)^2) (sq_nonneg _)) p.2) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  change (∫⁻ x, f x ∂((gaussianReal 0 1).prod μ.toMeasure).map (fun p => s p.2*p.1))=_
  have hfm : Measurable (fun p : ℝ×ℝ => f (s p.2*p.1)) := hf.comp (by fun_prop)
  rw [lintegral_map hf (by fun_prop),lintegral_prod_symm _ hfm.aemeasurable]
  have he : (fun t => ∫⁻ x, f (s t*x) ∂gaussianReal 0 1)=ᵐ[μ.toMeasure]
      fun t => ∫⁻ x, gaussianPDF 0 (NNReal.mk ((s t)^2) (sq_nonneg _)) x*f x := by
    filter_upwards [hp] with t ht
    have hv : (NNReal.mk ((s t)^2) (sq_nonneg _))≠0 := by
      intro h
      have h' : (s t)^2=0 := congrArg (fun v : NNReal => (v:ℝ)) h
      nlinarith
    have hm := standardNormal_affine_map 0 (s t)
    simp only [zero_add] at hm
    rw [← lintegral_map hf (by fun_prop),hm,gaussianReal_of_var_ne_zero _ hv]
    exact lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hf
  rw [lintegral_congr_ae he]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_normalScaleMixtureDensity μ s hs) hf]
  rw [lintegral_lintegral_swap (hD.mul (hf.comp measurable_snd)).aemeasurable]
  apply lintegral_congr
  intro x
  change (∫⁻ t, gaussianPDF 0 (NNReal.mk ((s t)^2) (sq_nonneg _)) x*f x ∂μ.toMeasure)=_
  rw [lintegral_mul_const _ (by
    unfold gaussianPDF gaussianPDFReal
    fun_prop)]
  rfl

theorem normalScaleMixtureDensity_pos (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (x : ℝ) :
    0<normalScaleMixtureDensity μ s x := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have hm : Measurable (fun t => gaussianPDF 0 (NNReal.mk ((s t)^2) (sq_nonneg _)) x) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  have he := (lintegral_eq_zero_iff hm).mp hz
  obtain ⟨t,ht,hzero⟩ := (hp.and he).exists
  have hv : (NNReal.mk ((s t)^2) (sq_nonneg _))≠0 := by
    intro h
    have h' : (s t)^2=0 := congrArg (fun v : NNReal => (v:ℝ)) h
    nlinarith
  exact (gaussianPDF_pos 0 hv x).ne' hzero

theorem normalScaleMixtureMarginal_equivalent_volume (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    normalScaleMixtureMarginal μ s ≪ volume ∧ volume ≪ normalScaleMixtureMarginal μ s := by
  rw [normalScaleMixtureMarginal_withDensity μ s hs hp]
  refine ⟨withDensity_absolutelyContinuous _ _,?_⟩
  exact withDensity_absolutelyContinuous'
    (measurable_normalScaleMixtureDensity μ s hs).aemeasurable
    (Filter.Eventually.of_forall fun x => (normalScaleMixtureDensity_pos μ s hs hp x).ne')

end Verification
