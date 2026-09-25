import Verification.StudentBivariate
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

end Papers.AnsariRockel2024
