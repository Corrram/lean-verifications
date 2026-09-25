import Verification.StudentConditionalDensity

open ProbabilityTheory MeasureTheory Set
open scoped ENNReal

namespace Papers.AnsariRockel2024

theorem student_precision_measure_update (ν : ℝ) (hν : 0<ν) (x : ℝ) :
    (gammaMeasure (ν/2) (ν/2)).withDensity
      (fun t => gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x)=
      ENNReal.ofReal (Verification.studentMarginalPDF ν x) • gammaMeasure (ν/2+1/2) (ν/2+x^2/2) :=
  Verification.student_precision_measure_update ν hν x

theorem student_joint_density_factorization (r : ℝ) (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (x y : ℝ) :
    ENNReal.ofReal (Verification.studentJointPDF r ν (x,y))=
      ENNReal.ofReal (Verification.studentMarginalPDF ν x)*Verification.studentConditionalDensity r ν x y :=
  Verification.student_joint_density_factorization hr ν hν (x,y)

theorem student_conditional_density_normalized (r : ℝ) (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (x : ℝ) :
    (∫⁻ y, Verification.studentConditionalDensity r ν x y)=1 :=
  Verification.studentConditionalDensity_integral hr ν hν x

end Papers.AnsariRockel2024
