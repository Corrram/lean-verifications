import Verification.StudentTailIntegral
import Verification.StudentTailThreshold
import Verification.TailAverage
import Verification.ContinuousCDFQuantile

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped Topology unitInterval

namespace Verification

theorem studentBivariate_lowerTail_raw {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).HasLowerTailDependence
      (2*ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0)
        (-(1-r)/Real.sqrt ((1-r^2)/(ν+1)))) := by
  let C := studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν
  let μ := marginal (studentTLaw (bivariateCorrelation r) ν hν) 0
  let N := marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0
  let f := fun x => ProbabilityTheory.cdf N (studentConditionalScore r ν x x)
  have hN : N=normalScaleMixtureMarginal
      (gammaProbability ((ν+1)/2) ((ν+1)/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹) :=
    gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef (by norm_num))
      (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) 0
  have hNc : Continuous (ProbabilityTheory.cdf N) :=
    student_marginal_cdf_continuous (r := 0) (by norm_num) (ν+1) (by positivity) 0
  have hμc : Continuous (ProbabilityTheory.cdf μ) :=
    student_marginal_cdf_continuous ⟨hr.1.le,hr.2.le⟩ ν hν 0
  have hμs : StrictMono (ProbabilityTheory.cdf μ) :=
    student_marginal_cdf_strictMono ⟨hr.1.le,hr.2.le⟩ ν hν 0
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hscore : Continuous (fun x => studentConditionalScore r ν x x) := by
    unfold studentConditionalScore
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  have hi : Integrable f μ := by
    apply Integrable.of_bound (hNc.comp hscore).measurable.aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs,abs_of_nonneg (ProbabilityTheory.cdf_nonneg _ _)]
      exact ProbabilityTheory.cdf_le_one _ _
  have hp (a : ℝ) : 0<μ.real (Iic a) := by
    rw [← ProbabilityTheory.cdf_eq_real]
    exact (strictCDF_mem_Ioo μ hμs a).1
  have hf : Tendsto f atBot (𝓝 (ProbabilityTheory.cdf N (-(1-r)/Real.sqrt ((1-r^2)/(ν+1))))) :=
    hNc.continuousAt.tendsto.comp (student_diagonal_score_tendsto hr hν)
  have hdiag (a : ℝ) : C.diagonal (cdfUnit μ a)=2*∫ x in Iic a,f x ∂μ := by
    rw [studentBivariate_diagonal_conditional hr ν hν a]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [f]
      rw [hN]
      exact studentConditionalDensity_cdf_standard hr ν hν x x
  have ht : Tendsto (fun a => C.lowerTailRatio (cdfUnit μ a)) atBot
      (𝓝 (2*ProbabilityTheory.cdf N (-(1-r)/Real.sqrt ((1-r^2)/(ν+1))))) := by
    have hh := (tendsto_lower_tail_average μ hi hp hf).const_mul 2
    convert hh using 1
    funext a
    rw [lowerTailRatio,hdiag]
    change (2*∫ x in Iic a,f x ∂μ)/ProbabilityTheory.cdf μ a=_
    rw [ProbabilityTheory.cdf_eq_real]
    ring
  have hh := ht.comp (continuousCDFQuantile_tendsto_zero μ hμc hμs)
  apply hh.congr'
  have hlt : ∀ᶠ u : I in 𝓝[>] (0:I),u<1 :=
    (eventually_lt_nhds (show (0:I)<1 by norm_num)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlt,(self_mem_nhdsWithin : ∀ᶠ u : I in 𝓝[>] (0:I),0<u)] with u hu1 hu0
  dsimp only [Function.comp_def]
  rw [show cdfUnit μ (continuousCDFQuantile μ hμc hμs u)=u from
    Subtype.ext (cdf_continuousCDFQuantile μ hμc hμs ⟨hu0,hu1⟩)]

theorem student_tail_threshold_standard {r ν : ℝ} (hr : r∈Ioo (-1) 1) (hν : 0<ν) :
    (1-r)/Real.sqrt ((1-r^2)/(ν+1))=Real.sqrt ((ν+1)*(1-r)/(1+r)) := by
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hp : 0<(1-r^2)/(ν+1) := by positivity
  have hplus : 0<1+r := by linarith [hr.1]
  have hminus : 0<1-r := by linarith [hr.2]
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  rw [div_pow,Real.sq_sqrt hp.le]
  field_simp
  ring

theorem studentBivariate_lowerTail_interior {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).HasLowerTailDependence
      (2-2*ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0)
        (Real.sqrt ((ν+1)*(1-r)/(1+r)))) := by
  have h := studentBivariate_lowerTail_raw hr ν hν
  rw [neg_div,student_tail_threshold_standard hr hν] at h
  have hN : marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0=
      normalScaleMixtureMarginal
        (gammaProbability ((ν+1)/2) ((ν+1)/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹) :=
    gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef (by norm_num))
      (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) 0
  rw [hN,normalScaleMixtureMarginal_cdf_neg _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure ((ν+1)/2) ((ν+1)/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))] at h
  rw [hN]
  convert h using 1
  ring

theorem studentBivariate_upperTail_interior {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).HasUpperTailDependence
      (2-2*ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0)
        (Real.sqrt ((ν+1)*(1-r)/(1+r)))) := by
  have hs := gaussianScaleMixture_radiallySymmetric ⟨hr.1.le,hr.2.le⟩
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))
  exact (hs.hasUpperTailDependence_iff _).mpr (studentBivariate_lowerTail_interior hr ν hν)

theorem studentBivariate_lowerTail {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (studentBivariate r hr ν hν).HasLowerTailDependence
      (if r=1 then 1 else if r= -1 then 0 else
        2-2*ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0)
          (Real.sqrt ((ν+1)*(1-r)/(1+r)))) := by
  by_cases h1 : r=1
  · subst r
    rw [ite_eq_left rfl,studentBivariate_one ν hν]
    exact hasLowerTailDependence_comonotonic
  rw [ite_eq_right h1]
  by_cases hn : r= -1
  · subst r
    rw [ite_eq_left rfl,studentBivariate_negative_one ν hν]
    exact hasLowerTailDependence_countermonotonic
  rw [ite_eq_right hn]
  exact studentBivariate_lowerTail_interior
    ⟨lt_of_le_of_ne hr.1 (Ne.symm hn),lt_of_le_of_ne hr.2 h1⟩ ν hν

theorem studentBivariate_upperTail {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (studentBivariate r hr ν hν).HasUpperTailDependence
      (if r=1 then 1 else if r= -1 then 0 else
        2-2*ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation 0) (ν+1) (by positivity)) 0)
          (Real.sqrt ((ν+1)*(1-r)/(1+r)))) := by
  have hs := gaussianScaleMixture_radiallySymmetric hr
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))
  exact (hs.hasUpperTailDependence_iff _).mpr (studentBivariate_lowerTail hr ν hν)

end Verification
