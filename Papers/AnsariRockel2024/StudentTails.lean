import Verification.StudentTailIntegral
import Verification.StudentTailLimit
import Papers.AnsariRockel2024.StudentConditional

open ProbabilityTheory MeasureTheory Set Copula

namespace Papers.AnsariRockel2024

theorem student_diagonal_integral (r : ℝ) (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (a : ℝ) :
    (Verification.studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).diagonal
      (cdfUnit (marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) 0) a)=
      2*∫ x in Iic a, ProbabilityTheory.cdf (marginal
        (studentTLaw (Verification.bivariateCorrelation 0) (ν+1) (by positivity)) 0)
        ((x-r*x)/Real.sqrt ((ν+x^2)*(1-r^2)/(ν+1)))
        ∂marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) 0 := by
  rw [Verification.studentBivariate_diagonal_conditional hr ν hν a]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => student_conditional_cdf_standard r hr ν hν x x

theorem student_lowerTailRatio_integral (r : ℝ) (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (a : ℝ) :
    (Verification.studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).lowerTailRatio
      (cdfUnit (marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) 0) a)=
      (2*∫ x in Iic a, ProbabilityTheory.cdf (marginal
        (studentTLaw (Verification.bivariateCorrelation 0) (ν+1) (by positivity)) 0)
        ((x-r*x)/Real.sqrt ((ν+x^2)*(1-r^2)/(ν+1)))
        ∂marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) 0)/
      ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) 0) a := by
  rw [lowerTailRatio,student_diagonal_integral r hr ν hν a]
  rfl

theorem student_lowerTail_interior (r : ℝ) (hr : r∈Ioo (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).HasLowerTailDependence
      (2-2*ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation 0) (ν+1) (by positivity)) 0)
        (Real.sqrt ((ν+1)*(1-r)/(1+r)))) :=
  Verification.studentBivariate_lowerTail_interior hr ν hν

theorem student_upperTail_interior (r : ℝ) (hr : r∈Ioo (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).HasUpperTailDependence
      (2-2*ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation 0) (ν+1) (by positivity)) 0)
        (Real.sqrt ((ν+1)*(1-r)/(1+r)))) :=
  Verification.studentBivariate_upperTail_interior hr ν hν

theorem student_lowerTail (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).HasLowerTailDependence
      (if r=1 then 1 else if r= -1 then 0 else
        2-2*ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation 0) (ν+1) (by positivity)) 0)
          (Real.sqrt ((ν+1)*(1-r)/(1+r)))) :=
  Verification.studentBivariate_lowerTail hr ν hν

theorem student_upperTail (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).HasUpperTailDependence
      (if r=1 then 1 else if r= -1 then 0 else
        2-2*ProbabilityTheory.cdf (marginal (studentTLaw (Verification.bivariateCorrelation 0) (ν+1) (by positivity)) 0)
          (Real.sqrt ((ν+1)*(1-r)/(1+r)))) :=
  Verification.studentBivariate_upperTail hr ν hν

end Papers.AnsariRockel2024
