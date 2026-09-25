import Mathlib.Analysis.Real.Pi.Bounds
import Verification.StudentJointDensity

open ProbabilityTheory MeasureTheory Real Set

namespace Verification

/-- Literal arXiv v3 HTML Table 1 expression, using correlation r in the printed dimension slots. -/
noncomputable def studentPrintedJointPDF (r ν : ℝ) (p : ℝ×ℝ) : ℝ :=
  Real.Gamma ((ν+r)/2)/(Real.Gamma (ν/2)*ν^(r/2)*Real.pi^(r/2)*Real.sqrt (1-r^2))*
    (1+studentQuadratic r p/ν)^(-((ν+r)/2))

theorem studentPrintedJointPDF_zero_two_origin : studentPrintedJointPDF 0 2 (0,0)=1 := by
  norm_num [studentPrintedJointPDF,studentQuadratic,Real.Gamma_one]

theorem studentJointPDF_zero_two_origin : studentJointPDF 0 2 (0,0)=(2*Real.pi)⁻¹ := by
  rw [studentJointPDF_standard_form (by norm_num) (by norm_num)]
  norm_num [studentQuadratic]

theorem student_joint_printed_formula_false :
    ¬∀ (r : ℝ) (_hr : r∈Ioo (-1) 1) (ν : ℝ) (_hν : 0<ν) (p : ℝ×ℝ),
      studentJointPDF r ν p=studentPrintedJointPDF r ν p := by
  intro h
  have he := h 0 (by norm_num) 2 (by norm_num) (0,0)
  rw [studentJointPDF_zero_two_origin,studentPrintedJointPDF_zero_two_origin] at he
  have hlt : (2*Real.pi)⁻¹<1 := (inv_lt_one₀ (by positivity)).mpr (by linarith [Real.pi_gt_three])
  exact (ne_of_lt hlt) he

end Verification
