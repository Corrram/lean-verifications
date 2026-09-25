import Verification.ScaleMixtureDensity

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

noncomputable def normalScaleMixtureAffineLaw (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (m : ℝ) : Measure ℝ :=
  ((gaussianReal 0 1).prod μ.toMeasure).map (fun p => m+s p.2*p.1)

theorem normalScaleMixtureAffineLaw_withDensity (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (m : ℝ) :
    normalScaleMixtureAffineLaw μ s m=volume.withDensity
      (fun x => ∫⁻ t, gaussianPDF m (NNReal.mk ((s t)^2) (sq_nonneg _)) x ∂μ.toMeasure) := by
  have hD : Measurable (fun p : ℝ×ℝ => gaussianPDF m (NNReal.mk ((s p.1)^2) (sq_nonneg _)) p.2) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  have hmix : Measurable (fun x => ∫⁻ t, gaussianPDF m (NNReal.mk ((s t)^2) (sq_nonneg _)) x ∂μ.toMeasure) := by
    apply Measurable.lintegral_prod_right
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  apply Measure.ext_of_lintegral
  intro f hf
  change (∫⁻ x, f x ∂((gaussianReal 0 1).prod μ.toMeasure).map (fun p => m+s p.2*p.1))=_
  have hfm : Measurable (fun p : ℝ×ℝ => f (m+s p.2*p.1)) := hf.comp (by fun_prop)
  rw [lintegral_map hf (by fun_prop),lintegral_prod_symm _ hfm.aemeasurable]
  have he : (fun t => ∫⁻ x, f (m+s t*x) ∂gaussianReal 0 1)=ᵐ[μ.toMeasure]
      fun t => ∫⁻ x, gaussianPDF m (NNReal.mk ((s t)^2) (sq_nonneg _)) x*f x := by
    filter_upwards [hp] with t ht
    have hv : (NNReal.mk ((s t)^2) (sq_nonneg _))≠0 := by
      intro h
      have h' : (s t)^2=0 := congrArg (fun v : NNReal => (v:ℝ)) h
      nlinarith
    rw [← lintegral_map hf (by fun_prop),standardNormal_affine_map,gaussianReal_of_var_ne_zero _ hv]
    exact lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hf
  rw [lintegral_congr_ae he,lintegral_withDensity_eq_lintegral_mul _ hmix hf,
    lintegral_lintegral_swap (hD.mul (hf.comp measurable_snd)).aemeasurable]
  apply lintegral_congr
  intro x
  change (∫⁻ t, gaussianPDF m (NNReal.mk ((s t)^2) (sq_nonneg _)) x*f x ∂μ.toMeasure)=_
  rw [lintegral_mul_const _ (by
    unfold gaussianPDF gaussianPDFReal
    fun_prop)]
  rfl

theorem normalScaleMixtureAffineLaw_cdf (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (m y : ℝ) :
    ProbabilityTheory.cdf (normalScaleMixtureAffineLaw μ s m) y=
      ∫ t, ProbabilityTheory.cdf (gaussianReal 0 1) ((y-m)/s t) ∂μ.toMeasure := by
  have hm : Measurable (fun p : ℝ×ℝ => s p.2*p.1) := by fun_prop
  have ha : Measurable (fun p : ℝ×ℝ => m+s p.2*p.1) := by fun_prop
  let : IsProbabilityMeasure (normalScaleMixtureMarginal μ s) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure (normalScaleMixtureAffineLaw μ s m) :=
    (Measure.isProbabilityMeasure_map_iff ha.aemeasurable).mpr inferInstance
  have he : normalScaleMixtureAffineLaw μ s m=(normalScaleMixtureMarginal μ s).map (fun x => m+x) := by
    unfold normalScaleMixtureAffineLaw normalScaleMixtureMarginal
    rw [Measure.map_map (by fun_prop) hm]
    rfl
  rw [ProbabilityTheory.cdf_eq_real,he,map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hset : (fun x : ℝ => m+x) ⁻¹' Iic y=Iic (y-m) := by
    ext x
    simp only [mem_preimage,mem_Iic]
    constructor <;> intro h <;> linarith
  rw [hset,← ProbabilityTheory.cdf_eq_real,normalScaleMixtureMarginal_cdf μ s hs hp]

end Verification
