import Verification.LTDExampleRanks
import Papers.Rockel2026XiFootrule.SIRegion

/-! # Remark 2.6(d): the printed matrix and a corrected LTD example

The printed matrix has the stated ranks, but is not LTD: at (2/3,2/3) its
CDF is 5/12, below 4/9. Replacing the lower block by masses 1/9,2/9,2/9,1/9
provides a genuine LTD copula with xi strictly larger than footrule.
-/

open ProbabilityTheory Set Matrix Verification.LTDExample
open Copula
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

noncomputable def printedLTDExample : Copula 2 := (thirdMatrix (1/4) (by norm_num)).checkerboard
noncomputable def correctedLTDExample : Copula 2 := (thirdMatrix (1/3) (by norm_num)).checkerboard

/-- Literal correspondence with the mass matrix printed in Remark 2.6(d). -/
theorem printed_ltd_matrix : (thirdMatrix (1/4) (by norm_num)).mass=
    !![1/3,0,0; 0,1/12,1/4; 0,1/4,1/12] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [thirdMatrix]

theorem printed_ltd_coefficients : printedLTDExample.chatterjeeXi=1/2 ∧
    printedLTDExample.spearmanFootrule=1/3 := by
  unfold printedLTDExample
  rw [thirdMatrix_xi,thirdMatrix_footrule]
  norm_num

/-- The literal LTD assertion in the printed example is false. -/
theorem printed_ltd_claim_false : ¬printedLTDExample.IsLTD := printedMatrix_not_ltd

/-- A corrected mass matrix giving the intended counterexample to xi<=footrule in LTD. -/
theorem corrected_ltd_matrix : (thirdMatrix (1/3) (by norm_num)).mass=
    !![1/3,0,0; 0,1/9,2/9; 0,2/9,1/9] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [thirdMatrix]

theorem corrected_ltd_counterexample : correctedLTDExample.IsLTD ∧
    correctedLTDExample.chatterjeeXi=38/81 ∧ correctedLTDExample.spearmanFootrule=10/27 ∧
    correctedLTDExample.spearmanFootrule < correctedLTDExample.chatterjeeXi := by
  refine ⟨correctedMatrix_ltd,?_⟩
  unfold correctedLTDExample
  rw [thirdMatrix_xi,thirdMatrix_footrule]
  norm_num

theorem corrected_ltd_not_si : ¬correctedLTDExample.IsSI := by
  intro h
  have hb := si_xi_le_footrule correctedLTDExample h
  exact (not_lt_of_ge hb) corrected_ltd_counterexample.2.2.2

end Papers.Rockel2026XiFootrule
