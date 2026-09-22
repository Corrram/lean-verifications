import Verification.RectangularXi

/-! # Proposition 3.3(iii) and Corollary 3.4 on arbitrary rectangular grids -/

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem patchwork_conditionalCDF (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (v : I) :
    (fun u => (A.patchwork C).conditionalCDF u v) =ᵐ[volume] Verification.patchworkKernel A C v :=
  Verification.patchwork_conditionalCDF A C v

theorem patchwork_xi_formula (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).chatterjeeXi =
      6*(∑ i, P.width i * ∑ j, Q.width j * ((Verification.cellPrefix A i j / P.width i)^2+
        (Verification.cellPrefix A i j / P.width i)*(A.mass i j / P.width i)+
        (A.mass i j / P.width i)^2*((C i j).chatterjeeXi+2)/6))-2 :=
  Verification.patchwork_xi_formula A C

theorem patchwork_xi_correction (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).chatterjeeXi = A.checkerboard.chatterjeeXi +
      ∑ i, ∑ j, Q.width j / P.width i * A.mass i j^2 * (C i j).chatterjeeXi :=
  Verification.patchwork_xi_correction A C

theorem rectangular_checkerboard_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkerboard.chatterjeeXi = (6*(m : ℝ)/(n : ℝ))*
      Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass * Verification.checkerboardXiMatrix n)-2 :=
  Verification.rectangular_checkerboard_xi hm hn A

theorem uniform_patchwork_xi_correction (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn))
    (C : Fin m → Fin n → Copula 2) :
    (A.patchwork C).chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * ∑ i, ∑ j, A.mass i j^2*(C i j).chatterjeeXi :=
  Verification.uniform_patchwork_xi_correction hm hn A C

theorem rectangular_perfect_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn))
    (C : Fin m → Fin n → Copula 2) (hC : ∀ i j, (C i j).chatterjeeXi=1) :
    (A.patchwork C).chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) :=
  Verification.rectangular_perfect_xi hm hn A C hC

theorem rectangular_checkMin_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkMin.chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) :=
  Verification.rectangular_checkMin_xi hm hn A

theorem rectangular_checkW_xi (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkW.chatterjeeXi = A.checkerboard.chatterjeeXi +
      (m : ℝ)/(n : ℝ) * Matrix.trace ((Matrix.of A.mass)ᵀ * Matrix.of A.mass) :=
  Verification.rectangular_checkW_xi hm hn A

theorem rectangular_xi_error_bound (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn))
    (C : Fin m → Fin n → Copula 2) :
    |(A.patchwork C).chatterjeeXi-A.checkerboard.chatterjeeXi| ≤
      if m ≤ n then (m : ℝ)/(n : ℝ)^2 else 1/(n : ℝ) :=
  Verification.rectangular_xi_error_bound hm hn A C

end Papers.Rockel2025Approximation
