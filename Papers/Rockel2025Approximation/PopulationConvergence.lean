import Verification.CheckerboardConvergence

/-! # Population convergence and an explicit empirical consistency criterion -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace Papers.Rockel2025Approximation

/-- Quantitative stability under CDF perturbations, for arbitrary partitions. -/
theorem checkerboard_xi_stability {m n : ℕ} (C D : Copula 2) (P : IntervalPartition m)
    (Q : IntervalPartition n) (ε : ℝ) (h : ∀ u v : I, |C.cdf ![u,v]-D.cdf ![u,v]| ≤ ε) :
    |(C.cellMass P Q).checkerboard.chatterjeeXi-(D.cellMass P Q).checkerboard.chatterjeeXi| ≤ 24*(m : ℝ)*ε :=
  Verification.checkerboard_xi_stability C D P Q ε h

/-- Population checkerboards converge in xi for every copula, including singular laws. -/
theorem checkerboard_xi_tendsto (C : Copula 2) :
    Tendsto (fun k => (C.cellMass (IntervalPartition.uniform (k+1) (by omega))
      (IntervalPartition.uniform (k+1) (by omega))).checkerboard.chatterjeeXi) atTop (𝓝 C.chatterjeeXi) :=
  Verification.checkerboard_xi_tendsto C

/-- The statistical CDF error rate is an explicit hypothesis, not an assumed conclusion. -/
theorem checkerboard_xi_tendsto_of_cdf_error (C : Copula 2) (D : ℕ → Copula 2)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (ε : ℕ → ℝ)
    (hCDF : ∀ᶠ k in atTop, ∀ u v, |(D k).cdf ![u,v]-C.cdf ![u,v]| ≤ ε k)
    (hε : Tendsto (fun k => ((N k : ℝ)+1)*ε k) atTop (𝓝 0)) :
    Tendsto (fun k => ((D k).cellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega))).checkerboard.chatterjeeXi) atTop (𝓝 C.chatterjeeXi) :=
  Verification.checkerboard_xi_tendsto_of_cdf_error C D N hN ε hCDF hε

theorem checkerboardEstimator_tendsto_of_cdf_error (C : Copula 2) (D : ℕ → Copula 2)
    (N : ℕ → ℕ) (hN : Tendsto N atTop atTop) (ε : ℕ → ℝ)
    (hCDF : ∀ᶠ k in atTop, ∀ u v, |(D k).cdf ![u,v]-C.cdf ![u,v]| ≤ ε k)
    (hε : Tendsto (fun k => ((N k : ℝ)+1)*ε k) atTop (𝓝 0)) :
    Tendsto (fun k => Verification.checkerboardEstimator ((D k).cellMass (IntervalPartition.uniform (N k+1) (by omega))
      (IntervalPartition.uniform (N k+1) (by omega)))) atTop (𝓝 C.chatterjeeXi) :=
  Verification.checkerboardEstimator_tendsto_of_cdf_error C D N hN ε hCDF hε

end Papers.Rockel2025Approximation
