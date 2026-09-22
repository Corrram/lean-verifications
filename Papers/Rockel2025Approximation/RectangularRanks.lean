import Verification.RectangularRho
import Verification.RectangularTau

/-! # Proposition 3.3(i)-(ii) for arbitrary rectangular cell matrices -/

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem rectangular_checkerboard_rho (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkerboard.spearmanRho =
      3*(∑ i : Fin m, ∑ j : Fin n,
        (((2*(m : ℝ)-2*((i : ℝ)+1)+1)*(2*(n : ℝ)-2*((j : ℝ)+1)+1))/((m : ℝ)*(n : ℝ))) * A.mass i j)-3 :=
  Verification.rectangular_checkerboard_rho hm hn A

theorem rectangular_checkMin_rho (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkMin.spearmanRho = A.checkerboard.spearmanRho+1/((m : ℝ)*(n : ℝ)) :=
  Verification.rectangular_checkMin_rho hm hn A

theorem rectangular_checkW_rho (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkW.spearmanRho = A.checkerboard.spearmanRho-1/((m : ℝ)*(n : ℝ)) :=
  Verification.rectangular_checkW_rho hm hn A

theorem rectangular_checkerboard_tau (A : CellMass P Q) :
    A.checkerboard.kendallTau = 1-Matrix.trace
      (Verification.checkerXiMatrix m * Matrix.of A.mass * Verification.checkerXiMatrix n * (Matrix.of A.mass)ᵀ) :=
  Verification.rectangular_checkerboard_tau A

theorem rectangular_checkMin_tau (A : CellMass P Q) :
    A.checkMin.kendallTau = A.checkerboard.kendallTau + Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) :=
  Verification.rectangular_checkMin_tau A

theorem rectangular_checkW_tau (A : CellMass P Q) :
    A.checkW.kendallTau = A.checkerboard.kendallTau - Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) :=
  Verification.rectangular_checkW_tau A

theorem patchwork_rho_correction (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).spearmanRho = A.checkerboard.spearmanRho +
      ∑ i, ∑ j, A.mass i j * P.width i * Q.width j * (C i j).spearmanRho :=
  Verification.patchwork_rho_correction A C

theorem patchwork_tau_correction (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).kendallTau = A.checkerboard.kendallTau +
      ∑ i, ∑ j, A.mass i j^2*(C i j).kendallTau :=
  Verification.patchwork_tau_correction A C

end Papers.Rockel2025Approximation
