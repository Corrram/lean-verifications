import Verification.CheckerboardMTP2

/-! # Theorem 4.2: checkerboard lower bound for Chatterjee's xi -/

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

/-- The source's MTP2 density implies conditional increase in both directions. -/
theorem mtp2_isCI {C : Copula 2} (hC : C.HasMTP2Density) : C.IsCI :=
  Verification.mtp2_isCI hC

/-- The comparison holds for CI copulas with any response partition. -/
theorem checkerboard_xi_le_of_isCI {n : ℕ} (C : Copula 2) (hC : C.IsCI)
    (m : ℕ) (hm : 0<m) (Q : IntervalPartition n) :
    (C.cellMass (IntervalPartition.uniform m hm) Q).checkerboard.chatterjeeXi ≤ C.chatterjeeXi :=
  Verification.checkerboard_xi_le_of_isCI C hC m hm Q

/-- Theorem 4.2, for every positive rectangular grid and its actual source cell masses. -/
theorem checkerboard_xi_le_of_mtp2 (C : Copula 2) (hC : C.HasMTP2Density)
    (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.cellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)).checkerboard.chatterjeeXi ≤
      C.chatterjeeXi :=
  Verification.checkerboard_xi_le_of_mtp2 C hC m hm (IntervalPartition.uniform n hn)

end Papers.Rockel2025Approximation
