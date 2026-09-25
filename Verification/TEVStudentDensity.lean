import Verification.TEVStudentCDF
import Verification.StudentMarginalDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Density and derivative of the Student-t CDF -/

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem studentMarginalPDF_continuous (k : ℝ) (hk : 0<k) : Continuous (studentMarginalPDF k) := by
  unfold studentMarginalPDF
  have hb : ∀ x : ℝ, 0<k/2+x^2/2 := fun x => by positivity
  have hc : Continuous (fun x : ℝ => (k/2+x^2/2)^(k/2+1/2)) :=
    (continuous_const.add ((continuous_pow 2).div_const 2)).rpow_const
      (fun x => Or.inl (hb x).ne')
  exact continuous_const.mul (continuous_const.div hc
    (fun x => (Real.rpow_pos_of_pos (hb x) _).ne'))

theorem studentMixture_withDensity (k : ℝ) (hk : 0<k) :
    normalScaleMixtureMarginal (gammaProbability (k/2) (k/2) (by positivity) (by positivity))
      (fun t => (Real.sqrt t)⁻¹)=volume.withDensity (fun x => ENNReal.ofReal (studentMarginalPDF k x)) := by
  rw [normalScaleMixtureMarginal_withDensity _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (k/2) (k/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))]
  congr 1
  funext x
  exact student_marginal_density_evaluation k hk x

theorem studentMarginalPDF_integrable (k : ℝ) (hk : 0<k) : Integrable (studentMarginalPDF k) := by
  have hP : IsProbabilityMeasure (normalScaleMixtureMarginal
      (gammaProbability (k/2) (k/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)) := by
    unfold normalScaleMixtureMarginal
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hone : (∫⁻ x, ENNReal.ofReal (studentMarginalPDF k x))=1 := by
    have h := hP.measure_univ
    rw [studentMixture_withDensity k hk,withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at h
    exact h
  apply (lintegral_ofReal_ne_top_iff_integrable
    (studentMarginalPDF_continuous k hk).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => (studentMarginalPDF_pos hk x).le)).mp
  rw [hone]
  exact ENNReal.one_ne_top

theorem studentMarginalPDF_lintegral (k : ℝ) (hk : 0<k) :
    (∫⁻ x, ENNReal.ofReal (studentMarginalPDF k x))=1 := by
  have hP : IsProbabilityMeasure (normalScaleMixtureMarginal
      (gammaProbability (k/2) (k/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)) := by
    unfold normalScaleMixtureMarginal
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have h := hP.measure_univ
  rw [studentMixture_withDensity k hk,withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h
  exact h

theorem studentMarginalPDF_integral (k : ℝ) (hk : 0<k) : (∫ x, studentMarginalPDF k x)=1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => (studentMarginalPDF_pos hk t).le)
    (studentMarginalPDF_continuous k hk).aestronglyMeasurable,studentMarginalPDF_lintegral k hk]
  simp

theorem studentTCDF_eq_integral_Iic (k : ℝ) (hk : 0<k) (x : ℝ) :
    studentTCDF k x=∫ t in Iic x, studentMarginalPDF k t := by
  have hP : IsProbabilityMeasure (normalScaleMixtureMarginal
      (gammaProbability (k/2) (k/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)) := by
    unfold normalScaleMixtureMarginal
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  rw [studentTCDF_eq_mixture_cdf k hk,ProbabilityTheory.cdf_eq_real,studentMixture_withDensity k hk,
    measureReal_def,withDensity_apply _ measurableSet_Iic,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => (studentMarginalPDF_pos hk t).le)
      (studentMarginalPDF_continuous k hk).aestronglyMeasurable]

theorem studentTCDF_hasDerivAt (k : ℝ) (hk : 0<k) (z : ℝ) :
    HasDerivAt (studentTCDF k) (studentMarginalPDF k z) z := by
  have hc := studentMarginalPDF_continuous k hk
  have hi := studentMarginalPDF_integrable k hk
  have he : studentTCDF k=fun x => studentTCDF k 0+∫ t in (0:ℝ)..x, studentMarginalPDF k t := by
    funext x
    rw [studentTCDF_eq_integral_Iic k hk x,studentTCDF_eq_integral_Iic k hk 0,
      ← intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn]
    ring
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_add _

theorem studentTCDF_continuous (k : ℝ) (hk : 0<k) : Continuous (studentTCDF k) :=
  continuous_iff_continuousAt.mpr fun z => (studentTCDF_hasDerivAt k hk z).continuousAt

end Verification
