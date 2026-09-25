import Verification.GaussianRho
import Copula.Rank.ConditionalCDF

/-! # The conditional CDF of a Gaussian copula in normal coordinates -/

open MeasureTheory ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem standardGaussian_lower_rectangle {r : ℝ} (hr : r∈Ioo (-1) 1) (a b : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ×ℝ | p.1≤a ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤b}=
      ∫ x in Iic a, ProbabilityTheory.cdf (gaussianReal 0 1)
        ((b-r*x)/Real.sqrt (1-r^2)) ∂gaussianReal 0 1 := by
  let μ := gaussianReal 0 1
  let S := {p : ℝ×ℝ | p.1≤a ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤b}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
        measurable_const)
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (μ.prod μ) :=
    (integrable_const _).indicator hS
  have hs : 0<Real.sqrt (1-r^2) := Real.sqrt_pos.2 (by nlinarith [hr.1,hr.2])
  change (μ.prod μ).real S=_
  rw [← integral_indicator_one hS]
  change (∫ p, S.indicator (fun _ => (1:ℝ)) p ∂μ.prod μ)=_
  rw [integral_prod _ hi,← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x≤a
    · rw [indicator_of_mem (show x∈Iic a from hx)]
      have hf (y : ℝ) : S.indicator (fun _ => (1:ℝ)) (x,y)=
          if Real.sqrt (1-r^2)*y≤b-r*x then (1:ℝ) else 0 := by
        simp only [S,indicator,mem_ofPred_eq,hx,true_and]
        congr 1
        apply propext
        constructor <;> intro h <;> linarith
      simp_rw [hf]
      exact standardGaussian_linear_halfline hs (b-r*x)
    · simp [S,indicator,hx]

theorem gaussianBivariate_cdf_normal {r : ℝ} (hr : r∈Ioo (-1) 1) (a b : ℝ) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).cdf
      ![cdfUnit (gaussianReal 0 1) a,cdfUnit (gaussianReal 0 1) b]=
      ∫ x in Iic a, ProbabilityTheory.cdf (gaussianReal 0 1)
        ((b-r*x)/Real.sqrt (1-r^2)) ∂gaussianReal 0 1 := by
  let μ := gaussianReal 0 1
  let S := {p : ℝ×ℝ | p.1≤a ∧ r*p.1+Real.sqrt (1-r^2)*p.2≤b}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_fst measurable_const).inter
      (measurableSet_le
        ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd))
        measurable_const)
  have hm : Measurable (fun x : Fin 2 → ℝ => ![cdfUnit μ (x 0),
      cdfUnit μ (r*x 0+Real.sqrt (1-r^2)*x 1)]) := by fun_prop
  rw [Copula.cdf]
  erw [gaussianBivariate_toMeasure_independent]
  rw [map_measureReal_apply hm measurableSet_Iic]
  have hset : (fun x : Fin 2 → ℝ => ![cdfUnit μ (x 0),
      cdfUnit μ (r*x 0+Real.sqrt (1-r^2)*x 1)]) ⁻¹'
      Iic ![cdfUnit μ a,cdfUnit μ b]=MeasurableEquiv.finTwoArrow ⁻¹' S := by
    ext x
    change (∀ i : Fin 2, (![cdfUnit μ (x 0),cdfUnit μ (r*x 0+Real.sqrt (1-r^2)*x 1)] i)≤
      (![cdfUnit μ a,cdfUnit μ b] i)) ↔ _
    simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    change (ProbabilityTheory.cdf μ (x 0)≤ProbabilityTheory.cdf μ a ∧
      ProbabilityTheory.cdf μ (r*x 0+Real.sqrt (1-r^2)*x 1)≤ProbabilityTheory.cdf μ b) ↔
      (x 0≤a ∧ r*x 0+Real.sqrt (1-r^2)*x 1≤b)
    simp only [μ,standardNormalCDF_strictMono.le_iff_le]
  rw [hset]
  have he := congrArg ENNReal.toReal
    ((measurePreserving_finTwoArrow μ).measure_preimage hS.nullMeasurableSet)
  change (Measure.pi (fun _ : Fin 2 => μ)).real (MeasurableEquiv.finTwoArrow ⁻¹' S)=
    (μ.prod μ).real S at he
  rw [he]
  exact standardGaussian_lower_rectangle hr a b

theorem ae_eq_of_nonneg_Iic_integrals {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f g : ℝ → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hnf : ∀ x, 0≤f x) (hng : ∀ x, 0≤g x)
    (he : ∀ a, (∫ x in Iic a, f x ∂μ)=∫ x in Iic a, g x ∂μ) : f=ᵐ[μ]g := by
  have := isFiniteMeasure_withDensity_ofReal hf.2
  have := isFiniteMeasure_withDensity_ofReal hg.2
  have hm : μ.withDensity (fun x => ENNReal.ofReal (f x))=
      μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
    apply Measure.ext_of_Iic
    intro a
    rw [withDensity_apply _ measurableSet_Iic,withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hnf),
      ← ofReal_integral_eq_lintegral_ofReal hg.integrableOn (Filter.Eventually.of_forall hng),he]
  have ha := (withDensity_eq_iff_of_sigmaFinite
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hg.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp hm
  filter_upwards [ha] with x hx
  have h := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (hnf x),ENNReal.toReal_ofReal (hng x)] using h

theorem gaussianBivariate_conditionalCDF_normal {r : ℝ} (hr : r∈Ioo (-1) 1) (b : ℝ) :
    (fun x => (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).conditionalCDF
      (cdfUnit (gaussianReal 0 1) x) (cdfUnit (gaussianReal 0 1) b)) =ᵐ[gaussianReal 0 1]
      fun x => ProbabilityTheory.cdf (gaussianReal 0 1) ((b-r*x)/Real.sqrt (1-r^2)) := by
  let μ := gaussianReal 0 1
  let C := gaussianBivariate r ⟨hr.1.le,hr.2.le⟩
  have hmp := measurePreserving_cdfUnit μ continuous_standardNormalCDF
  have hK := hmp.integrable_comp_of_integrable (C.integrable_conditionalCDF (cdfUnit μ b))
  have hf : Integrable (fun x => ProbabilityTheory.cdf μ ((b-r*x)/Real.sqrt (1-r^2))) μ := by
    apply (integrable_const (1:ℝ)).mono'
      (((monotone_cdf μ).measurable.comp
        (show Measurable (fun x : ℝ => (b-r*x)/Real.sqrt (1-r^2)) by fun_prop)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg μ _)]
      exact cdf_le_one μ _
  apply ae_eq_of_nonneg_Iic_integrals hK hf
    (fun x => C.conditionalCDF_nonneg _ _) (fun x => cdf_nonneg μ _)
  intro a
  have hpre : (cdfUnit μ) ⁻¹' Iic (cdfUnit μ a)=Iic a := by
    ext x
    change ProbabilityTheory.cdf μ x≤ProbabilityTheory.cdf μ a ↔ x≤a
    exact standardNormalCDF_strictMono.le_iff_le
  have he := setIntegral_map (μ := μ) (g := cdfUnit μ)
    (f := fun u => C.conditionalCDF u (cdfUnit μ b))
    (s := Iic (cdfUnit μ a)) measurableSet_Iic
    (C.measurable_conditionalCDF_left _).aestronglyMeasurable hmp.measurable.aemeasurable
  rw [hmp.map_eq,hpre] at he
  dsimp only [Function.comp_def]
  rw [← he,← C.cdf_eq_integral_conditionalCDF]
  exact gaussianBivariate_cdf_normal hr a b

theorem integral_standardNormal_transform {f : I → ℝ} (hf : AEStronglyMeasurable f volume) :
    (∫ u : I, f u)=∫ x, f (cdfUnit (gaussianReal 0 1) x) ∂gaussianReal 0 1 := by
  have hm := map_cdfUnit (gaussianReal 0 1) continuous_standardNormalCDF
  calc
    _ = ∫ u, f u ∂(gaussianReal 0 1).map (cdfUnit (gaussianReal 0 1)) := by rw [hm]
    _ = _ := integral_map (measurable_cdfUnit _).aemeasurable (by rwa [hm])

theorem gaussianBivariate_xi_normal_integral {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).chatterjeeXi=
      6*(∫ b, ∫ x, (ProbabilityTheory.cdf (gaussianReal 0 1)
        ((b-r*x)/Real.sqrt (1-r^2)))^2 ∂gaussianReal 0 1 ∂gaussianReal 0 1)-2 := by
  let C := gaussianBivariate r ⟨hr.1.le,hr.2.le⟩
  change C.chatterjeeXi=_
  rw [chatterjeeXi,integral_standardNormal_transform
    C.integrable_integral_conditionalCDF_sq.aestronglyMeasurable]
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun b => by
    dsimp only
    rw [integral_standardNormal_transform
      ((C.measurable_conditionalCDF_left _).pow_const 2).aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [gaussianBivariate_conditionalCDF_normal hr b] with x hx
    rw [hx]

end Verification
