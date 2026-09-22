import Verification.CheckerboardEstimator
import Verification.FiniteMajorization

/-! # Checked proof steps toward Theorems 4.2 and 4.5 -/

open MeasureTheory ProbabilityTheory Set Filter Matrix
open Copula
open scoped unitInterval BigOperators Topology

namespace Papers.Rockel2025Approximation

variable {n : ℕ}
variable (A : CellMass (IntervalPartition.uniform (n+1) (by omega)) (IntervalPartition.uniform (n+1) (by omega)))

theorem checkerboardEstimator_eq_average :
    Verification.checkerboardEstimator A = (A.checkerboard.chatterjeeXi+A.checkMin.chatterjeeXi)/2 :=
  Verification.checkerboardEstimator_eq_average A

theorem checkerboardEstimator_mem : Verification.checkerboardEstimator A ∈ Icc (0 : ℝ) 1 :=
  Verification.checkerboardEstimator_mem A

theorem checkerboardEstimator_correction_bounds :
    0 ≤ Verification.checkerboardEstimator A-A.checkerboard.chatterjeeXi ∧
      Verification.checkerboardEstimator A-A.checkerboard.chatterjeeXi ≤ (1/((n : ℝ)+1))/2 :=
  Verification.checkerboardEstimator_correction_bounds A

theorem checkerboardEstimator_correction_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (A : ∀ k, CellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega))) :
    Tendsto (fun k => Verification.checkerboardEstimator (A k)-(A k).checkerboard.chatterjeeXi) atTop (𝓝 0) :=
  Verification.checkerboardEstimator_correction_tendsto N hN A

theorem checkerboardEstimator_tendsto_iff (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (A : ∀ k, CellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega))) (l : ℝ) :
    Tendsto (fun k => Verification.checkerboardEstimator (A k)) atTop (𝓝 l) ↔
      Tendsto (fun k => (A k).checkerboard.chatterjeeXi) atTop (𝓝 l) :=
  Verification.checkerboardEstimator_tendsto_iff N hN A l

theorem majorization_sum_sq (a b : ℕ → ℝ) (n : ℕ)
    (hb : ∀ i, i < n-1 → b (i+1) ≤ b i)
    (hp : ∀ k, k ≤ n → (∑ i ∈ Finset.range k, b i) ≤ ∑ i ∈ Finset.range k, a i)
    (ht : (∑ i ∈ Finset.range n, a i) = ∑ i ∈ Finset.range n, b i) :
    (∑ i ∈ Finset.range n, b i^2) ≤ ∑ i ∈ Finset.range n, a i^2 :=
  Verification.majorization_sum_sq a b n hb hp ht

end Papers.Rockel2025Approximation
