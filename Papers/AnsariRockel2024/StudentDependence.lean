import Verification.StudentNonCI

open ProbabilityTheory Set Copula

namespace Papers.AnsariRockel2024

theorem student_isSI_iff (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).IsSI ↔ r=1 :=
  Verification.studentBivariate_isSI_iff hr ν hν

theorem student_isCI_iff (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).IsCI ↔ r=1 :=
  Verification.studentBivariate_isCI_iff hr ν hν

theorem student_isSD_iff (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).IsSD ↔ r= -1 :=
  Verification.studentBivariate_isSD_iff hr ν hν

theorem student_isCD_iff (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).IsCD ↔ r= -1 :=
  Verification.studentBivariate_isCD_iff hr ν hν

theorem student_not_hasMTP2Density (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    ¬(Verification.studentBivariate r hr ν hν).HasMTP2Density :=
  Verification.studentBivariate_not_hasMTP2Density hr ν hν

end Papers.AnsariRockel2024
