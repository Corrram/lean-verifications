import Verification.RectangularTails

/-! # All tail limits in Proposition 3.3 -/

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

variable {m n : ℕ}
variable (A : CellMass (IntervalPartition.uniform (m+1) (by omega)) (IntervalPartition.uniform (n+1) (by omega)))

theorem rectangular_checkerboard_lower_tail : A.checkerboard.HasLowerTailDependence 0 :=
  Verification.rectangular_checkerboard_lower_tail A

theorem rectangular_checkerboard_upper_tail : A.checkerboard.HasUpperTailDependence 0 :=
  Verification.rectangular_checkerboard_upper_tail A

theorem rectangular_checkMin_lower_tail :
    A.checkMin.HasLowerTailDependence (A.mass 0 0 * min ((m : ℝ)+1) ((n : ℝ)+1)) :=
  Verification.rectangular_checkMin_lower_tail A

theorem rectangular_checkMin_upper_tail :
    A.checkMin.HasUpperTailDependence (A.mass (Fin.last m) (Fin.last n) * min ((m : ℝ)+1) ((n : ℝ)+1)) :=
  Verification.rectangular_checkMin_upper_tail A

theorem rectangular_checkW_lower_tail : A.checkW.HasLowerTailDependence 0 :=
  Verification.rectangular_checkW_lower_tail A

theorem rectangular_checkW_upper_tail : A.checkW.HasUpperTailDependence 0 :=
  Verification.rectangular_checkW_upper_tail A

end Papers.Rockel2025Approximation
