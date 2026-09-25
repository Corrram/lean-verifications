import Verification.ScaleMixtureMarginals
import Verification.GaussianQuadrant
import Verification.GaussianReflection

open ProbabilityTheory MeasureTheory Set Copula

namespace Verification

noncomputable def normalScaleMixtureMarginal (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) : Measure ℝ :=
  ((gaussianReal 0 1).prod μ.toMeasure).map (fun p : ℝ×ℝ => s p.2*p.1)

theorem normalScaleMixtureMarginal_cdf (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (a : ℝ) :
    ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s) a=
      ∫ t, ProbabilityTheory.cdf (gaussianReal 0 1) (a/s t) ∂μ.toMeasure := by
  let G := gaussianReal 0 1
  have hm : Measurable (fun p : ℝ×ℝ => s p.2*p.1) := by fun_prop
  let : IsProbabilityMeasure (normalScaleMixtureMarginal μ s) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  let A := {p : ℝ×ℝ | s p.2*p.1≤a}
  have hA : MeasurableSet A := measurableSet_le hm measurable_const
  have hi : Integrable (A.indicator (fun _ => (1:ℝ))) (G.prod μ.toMeasure) :=
    (integrable_const _).indicator hA
  rw [ProbabilityTheory.cdf_eq_real]
  change ((G.prod μ.toMeasure).map (fun p : ℝ×ℝ => s p.2*p.1)).real (Iic a)=_
  rw [map_measureReal_apply hm measurableSet_Iic]
  change (G.prod μ.toMeasure).real A=_
  rw [← integral_indicator_one hA]
  change (∫ p, A.indicator (fun _ => (1:ℝ)) p ∂G.prod μ.toMeasure)=_
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hp] with t ht
  change (∫ x, (if s t*x≤a then (1:ℝ) else 0) ∂G)=_
  exact standardGaussian_linear_halfline ht a

theorem integrable_normalScaleMixture_cdf (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (a : ℝ) :
    Integrable (fun t => ProbabilityTheory.cdf (gaussianReal 0 1) (a/s t)) μ.toMeasure := by
  have hm : Measurable (fun t => ProbabilityTheory.cdf (gaussianReal 0 1) (a/s t)) :=
    (monotone_cdf (gaussianReal 0 1)).measurable.comp (measurable_const.div hs)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs,abs_of_nonneg (ProbabilityTheory.cdf_nonneg _ _)]
    exact ProbabilityTheory.cdf_le_one _ _

theorem normalScaleMixtureMarginal_cdf_strictMono (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    StrictMono (ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s)) := by
  intro a b hab
  rw [normalScaleMixtureMarginal_cdf μ s hs hp,normalScaleMixtureMarginal_cdf μ s hs hp]
  have hi := integrable_normalScaleMixture_cdf μ s hs
  have hlt : ∀ᵐ t ∂μ.toMeasure, ProbabilityTheory.cdf (gaussianReal 0 1) (a/s t)<
      ProbabilityTheory.cdf (gaussianReal 0 1) (b/s t) := by
    filter_upwards [hp] with t ht
    exact standardNormalCDF_strictMono ((div_lt_div_iff_of_pos_right ht).mpr hab)
  have hle := hlt.mono (fun _ h => h.le)
  apply lt_of_le_of_ne (integral_mono_ae (hi a) (hi b) hle)
  intro he
  have hae := (integral_eq_iff_of_ae_le (hi a) (hi b) hle).mp he
  obtain ⟨t,ht,heq⟩ := (hlt.and hae).exists
  exact (ne_of_lt ht) heq

theorem normalScaleMixtureMarginal_cdf_neg (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (a : ℝ) :
    ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s) (-a)=
      1-ProbabilityTheory.cdf (normalScaleMixtureMarginal μ s) a := by
  rw [normalScaleMixtureMarginal_cdf μ s hs hp,normalScaleMixtureMarginal_cdf μ s hs hp]
  simp_rw [neg_div,standardNormalCDF_neg]
  rw [integral_sub (integrable_const _) (integrable_normalScaleMixture_cdf μ s hs a)]
  simp

end Verification
