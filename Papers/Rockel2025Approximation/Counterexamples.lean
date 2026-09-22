import Verification.ApproximationExamples

/-! # Explicit counterexamples in Section 4.1 -/

open MeasureTheory ProbabilityTheory Set
open Copula Verification.ApproximationExamples
open scoped unitInterval

namespace Papers.Rockel2025Approximation

theorem example43 :
    lowerMatrix.checkerboard.IsSI ∧ lowerMatrix.checkerboard.chatterjeeXi=1/16 ∧
    (lowerMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkerboard.chatterjeeXi=1/8 ∧
    lowerMatrix.checkerboard.chatterjeeXi <
      (lowerMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
        (IntervalPartition.uniform 2 (by omega))).checkerboard.chatterjeeXi :=
  Verification.ApproximationExamples.lower_counterexample

theorem example44 :
    upperMatrix.checkerboard.HasMTP2Density ∧ upperMatrix.checkerboard.chatterjeeXi=5/8 ∧
    (upperMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkMin.chatterjeeXi=7/16 ∧
    (upperMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkMin.chatterjeeXi < upperMatrix.checkerboard.chatterjeeXi :=
  Verification.ApproximationExamples.upper_counterexample

theorem permutation_counterexample :
    shuffleMatrix.checkMin.chatterjeeXi=1 ∧
    (shuffleMatrix.checkMin.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkMin.chatterjeeXi=1/4 :=
  Verification.ApproximationExamples.shuffle_counterexample

end Papers.Rockel2025Approximation
