import Verification.GaussianRhoIntegral
import Verification.ScaleMixtureReflection

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussian_mixtureCDF_product_integral {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (a : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 2),
      ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s) (a*x 0)*
      ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s) (a*x 1)
        ∂multivariateGaussian 0 (bivariateCorrelation r))=
      ∫ t : ℝ×ℝ, 1/4+Real.arcsin
        (r*a^2/(Real.sqrt (a^2+(s t.1)^2)*Real.sqrt (a^2+(s t.2)^2)))/(2*Real.pi)
          ∂μ.toMeasure.prod μ.toMeasure := by
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let f := fun p : EuclideanSpace ℝ (Fin 2)×(ℝ×ℝ) =>
    ProbabilityTheory.cdf (gaussianReal 0 1) (a*p.1 0/s p.2.1)*
      ProbabilityTheory.cdf (gaussianReal 0 1) (a*p.1 1/s p.2.2)
  have hf : Measurable f :=
    ((monotone_cdf (gaussianReal 0 1)).measurable.comp (by fun_prop)).mul
      ((monotone_cdf (gaussianReal 0 1)).measurable.comp (by fun_prop))
  have hi : Integrable f (G.prod (μ.toMeasure.prod μ.toMeasure)) := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ProbabilityTheory.cdf_nonneg _ _)
        (ProbabilityTheory.cdf_nonneg _ _))]
      exact (mul_le_mul (ProbabilityTheory.cdf_le_one _ _) (ProbabilityTheory.cdf_le_one _ _)
        (ProbabilityTheory.cdf_nonneg _ _) zero_le_one).trans_eq (one_mul 1)
  have he (x : EuclideanSpace ℝ (Fin 2)) :
      ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s) (a*x 0)*
        ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s) (a*x 1)=
          ∫ t, f (x,t) ∂μ.toMeasure.prod μ.toMeasure := by
    rw [normalScaleMixtureMarginal_cdf μ s hs hp,normalScaleMixtureMarginal_cdf μ s hs hp]
    exact (integral_prod_mul _ _).symm
  simp_rw [he]
  rw [← integral_prod _ hi,integral_prod_symm _ hi]
  apply integral_congr_ae
  have hpos : ∀ᵐ t ∂μ.toMeasure.prod μ.toMeasure,0<s t.1 ∧ 0<s t.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_lt measurable_const (hs.comp measurable_fst)).inter
        (measurableSet_lt measurable_const (hs.comp measurable_snd)))).mpr
    filter_upwards [hp] with b hb
    filter_upwards [hp] with c hc
    exact ⟨hb,hc⟩
  filter_upwards [hpos] with t ht
  exact gaussian_cdf_product_integral hr a (s t.1) (s t.2) ht.1 ht.2

theorem gaussianScaleMixture_spearmanRho_integral {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).spearmanRho=
      12*(∫ a, ∫ t : ℝ×ℝ, 1/4+Real.arcsin
        (r*(s a)^2/(Real.sqrt ((s a)^2+(s t.1)^2)*Real.sqrt ((s a)^2+(s t.2)^2)))/(2*Real.pi)
          ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure)-3 := by
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let M := normalScaleMixtureMarginal μ s
  let f := fun p : EuclideanSpace ℝ (Fin 2)×ℝ =>
    ProbabilityTheory.cdf M (s p.2*p.1 0)*ProbabilityTheory.cdf M (s p.2*p.1 1)
  have hf : Measurable f :=
    ((monotone_cdf M).measurable.comp (by fun_prop)).mul
      ((monotone_cdf M).measurable.comp (by fun_prop))
  have hi : Integrable f (G.prod μ.toMeasure) := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ProbabilityTheory.cdf_nonneg _ _)
        (ProbabilityTheory.cdf_nonneg _ _))]
      exact (mul_le_mul (ProbabilityTheory.cdf_le_one _ _) (ProbabilityTheory.cdf_le_one _ _)
        (ProbabilityTheory.cdf_nonneg _ _) zero_le_one).trans_eq (one_mul 1)
  have hmap : Measurable (fun p : EuclideanSpace ℝ (Fin 2)×ℝ => fun i => cdfUnit M (s p.2*p.1 i)) := by fun_prop
  have hprod : Measurable (fun u : Fin 2 → I => (u 0:ℝ)*(u 1:ℝ)) := by fun_prop
  rw [spearmanRho,gaussianScaleMixture_toMeasure hr μ s hs hp,
    integral_map hmap.aemeasurable hprod.aestronglyMeasurable]
  change 12*(∫ p, f p ∂G.prod μ.toMeasure)-3=_
  rw [integral_prod_symm _ hi]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => gaussian_mixtureCDF_product_integral hr μ s hs hp (s a)

theorem integrable_arcsin_comp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hf : Measurable f) :
    Integrable (fun x => Real.arcsin (f x)) μ := by
  apply Integrable.of_bound (Real.continuous_arcsin.measurable.comp hf).aestronglyMeasurable (Real.pi/2)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin _,Real.arcsin_le_pi_div_two _⟩

theorem gaussianScaleMixture_spearmanRho {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).spearmanRho=
      6/Real.pi*(∫ a, ∫ t : ℝ×ℝ, Real.arcsin
        (r*(s a)^2/(Real.sqrt ((s a)^2+(s t.1)^2)*Real.sqrt ((s a)^2+(s t.2)^2)))
          ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure) := by
  let f := fun p : ℝ×(ℝ×ℝ) => Real.arcsin
    (r*(s p.1)^2/(Real.sqrt ((s p.1)^2+(s p.2.1)^2)*Real.sqrt ((s p.1)^2+(s p.2.2)^2)))
  have hi : Integrable f (μ.toMeasure.prod (μ.toMeasure.prod μ.toMeasure)) :=
    integrable_arcsin_comp _ _ (by fun_prop)
  have ha (a : ℝ) : Integrable (fun t : ℝ×ℝ => f (a,t)) (μ.toMeasure.prod μ.toMeasure) :=
    integrable_arcsin_comp _ _ (by fun_prop)
  have he (a : ℝ) : (∫ t : ℝ×ℝ, 1/4+f (a,t)/(2*Real.pi) ∂μ.toMeasure.prod μ.toMeasure)=
      1/4+(∫ t, f (a,t) ∂μ.toMeasure.prod μ.toMeasure)/(2*Real.pi) := by
    rw [integral_add (integrable_const _) ((ha a).div_const _)]
    simp only [integral_div,integral_const,probReal_univ,one_smul]
  rw [gaussianScaleMixture_spearmanRho_integral hr μ s hs hp]
  change 12*(∫ a, ∫ t, 1/4+f (a,t)/(2*Real.pi) ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure)-3=_
  simp_rw [he]
  rw [integral_add (integrable_const _) (hi.integral_prod_left.div_const _)]
  simp only [integral_div,integral_const,probReal_univ,one_smul]
  change 12*(1/4+(∫ a, ∫ t, f (a,t) ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure)/(2*Real.pi))-3=
    6/Real.pi*(∫ a, ∫ t, f (a,t) ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure)
  ring

end Verification
