import Verification.StudentBivariate
import Verification.StudentNegativeEndpoint
import Verification.ScaleMixtureMarginals
import Verification.ScaleMixtureCDF
import Copula.Dependence.ConditionalMonotonicity

open ProbabilityTheory MeasureTheory Set Copula

namespace Papers.AnsariRockel2024

theorem student_isSklarCopula (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    IsSklarCopula (studentTLaw (Verification.bivariateCorrelation r) ν hν)
      (Verification.studentBivariate r hr ν hν) :=
  Verification.studentBivariate_isSklarCopula r hr ν hν

theorem student_one (ν : ℝ) (hν : 0<ν) :
    Verification.studentBivariate 1 (by norm_num) ν hν=comonotonic 2 :=
  Verification.studentBivariate_one ν hν

theorem student_one_isCI (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate 1 (by norm_num) ν hν).IsCI := by
  rw [student_one ν hν]
  exact isCI_comonotonic

theorem student_negative_one (ν : ℝ) (hν : 0<ν) :
    Verification.studentBivariate (-1) (by norm_num) ν hν=countermonotonic :=
  Verification.studentBivariate_negative_one ν hν

theorem student_negative_one_isCD (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate (-1) (by norm_num) ν hν).IsCD := by
  rw [student_negative_one ν hν]
  exact isCD_countermonotonic

theorem student_marginal (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i=
      ((gaussianReal 0 1).prod
        (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)).toMeasure).map
          (fun p : ℝ×ℝ => (Real.sqrt p.2)⁻¹*p.1) :=
  Verification.gaussianScaleMixtureLaw_marginal _ (Verification.bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) i

theorem student_marginal_cdf (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) (i : Fin 2) (a : ℝ) :
    ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i) a=
      ∫ t, ProbabilityTheory.cdf (gaussianReal 0 1) (a*Real.sqrt t)
        ∂(gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)).toMeasure := by
  rw [student_marginal r hr ν hν i]
  have h := Verification.normalScaleMixtureMarginal_cdf
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) a
  simpa only [Verification.normalScaleMixtureMarginal,div_inv_eq_mul] using h

theorem student_marginal_cdf_strictMono (r : ℝ) (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    StrictMono (ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i)) := by
  rw [student_marginal r hr ν hν i]
  exact Verification.normalScaleMixtureMarginal_cdf_strictMono
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹) (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem student_marginal_cdf_neg (r : ℝ) (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) (i : Fin 2) (a : ℝ) :
    ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i) (-a)=
      1-ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i) a := by
  rw [student_marginal r hr ν hν i]
  exact Verification.normalScaleMixtureMarginal_cdf_neg
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹) (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) a

end Papers.AnsariRockel2024
