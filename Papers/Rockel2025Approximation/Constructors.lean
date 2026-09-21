import Copula.Bernstein
import Copula.Checkerboard

/-! # Valid approximation families and deterministic uniform convergence

These constructors allow arbitrary source copulas, including singular laws.
Uniform CDF convergence is distinct from the statistical and xi convergence
claims of Section 4, which require additional work.
-/

open ProbabilityTheory Filter
open Copula
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

theorem bernstein_cdf (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (u v : I) :
    (C.bernstein m n hm hn).cdf ![u, v] =
      ∑ i : Fin (m + 1), ∑ j : Fin (n + 1),
        C.cdf ![_root_.bernstein.z i, _root_.bernstein.z j] *
          _root_.bernstein m i u * _root_.bernstein n j v := by
  rw [cdf_bernstein]
  exact C.bernsteinCDF_eq_sum m n u v

theorem bernstein_uniform_error (C : Copula 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (u v : I) :
    |(C.bernstein m n hm hn).cdf ![u, v] - C.cdf ![u, v]| ≤
      Real.sqrt (1 / (4 * (m : ℝ))) + Real.sqrt (1 / (4 * (n : ℝ))) := by
  rw [cdf_bernstein]
  exact C.abs_bernsteinCDF_sub_le_uniform m n hm hn u v

theorem bernstein_uniform_convergence (C : Copula 2) :
    TendstoUniformly (fun k : ℕ => (C.bernstein (k + 1) (k + 1)
      (Nat.succ_pos k) (Nat.succ_pos k)).cdf) C.cdf atTop := C.tendstoUniformly_bernstein

theorem rectangular_checkerboard_cdf {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}
    (A : CellMass P Q) (u v : I) :
    A.checkerboard.cdf ![u, v] =
      ∑ i, ∑ j, A.mass i j * (P.coord i u : ℝ) * (Q.coord j v : ℝ) := by
  simpa only [mul_assoc] using A.cdf_checkerboard u v

theorem rectangular_checkMin_cdf {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}
    (A : CellMass P Q) (u v : I) :
    A.checkMin.cdf ![u, v] =
      ∑ i, ∑ j, A.mass i j * min (P.coord i u : ℝ) (Q.coord j v : ℝ) := A.cdf_checkMin u v

theorem rectangular_checkW_cdf {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}
    (A : CellMass P Q) (u v : I) :
    A.checkW.cdf ![u, v] =
      ∑ i, ∑ j, A.mass i j * max ((P.coord i u : ℝ) + (Q.coord j v : ℝ) - 1) 0 := A.cdf_checkW u v

/-- Arbitrary local fillings preserve source values at every grid vertex. -/
theorem patchwork_grid_interpolation (C : Copula 2) {m n : ℕ}
    (P : IntervalPartition m) (Q : IntervalPartition n)
    (D : Fin m → Fin n → Copula 2) (i : Fin (m + 1)) (j : Fin (n + 1)) :
    ((C.cellMass P Q).patchwork D).cdf ![P.point i, Q.point j] =
      C.cdf ![P.point i, Q.point j] := C.cdf_cellMass_patchwork_point P Q D i j

/-- Deterministic CDF convergence, simultaneously for checkerboard, check-min and check-W fillings. -/
theorem patchwork_uniform_convergence (C : Copula 2)
    (D : (k : ℕ) → Fin (k + 1) → Fin (k + 1) → Copula 2) :
    TendstoUniformly (fun k : ℕ =>
      ((C.cellMass (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))
        (IntervalPartition.uniform (k + 1) (Nat.succ_pos k))).patchwork (D k)).cdf)
      C.cdf atTop := C.tendstoUniformly_cellMass_patchwork D

end Papers.Rockel2025Approximation
