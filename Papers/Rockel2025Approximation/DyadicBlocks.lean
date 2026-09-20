import Papers.Rockel2025Approximation.Definitions
import Copula.OrdinalSum.Rank

/-! # Proposition 3.3 on diagonal dyadic grids

At depth n there are 2^n equal diagonal cells, each of mass 1/2^n.
Choosing independence, M, or W inside each cell gives the checkerboard,
check-min, or check-w copula for that grid. General matrices and xi formulas
are not claimed here.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2025Approximation

/-- Fill each diagonal cell of a dyadic grid with a rescaled copy of C. -/
noncomputable def dyadicBlocks : ℕ → Copula 2 → Copula 2
  | 0, C => C
  | n + 1, C => (dyadicBlocks n C).ordinalSum (dyadicBlocks n C) Copula.unitHalf

/-- Exact recursive CDF, including the edges and the midpoint. -/
theorem dyadicBlocks_cdf (n : ℕ) (C : Copula 2) (u v : I) :
    (dyadicBlocks (n + 1) C).cdf ![u, v] =
      (1 / 2 : ℝ) * (dyadicBlocks n C).cdf
        ![Copula.OrdinalSum.lowerCoord Copula.unitHalf u,
          Copula.OrdinalSum.lowerCoord Copula.unitHalf v] +
      (1 / 2 : ℝ) * (dyadicBlocks n C).cdf
        ![Copula.OrdinalSum.upperCoord Copula.unitHalf u,
          Copula.OrdinalSum.upperCoord Copula.unitHalf v] := by
  simp only [dyadicBlocks, Copula.cdf_ordinalSum, Copula.ordinalSumCDF,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num [Copula.unitHalf]

theorem dyadicBlocks_rho (n : ℕ) (C : Copula 2) :
    (dyadicBlocks n C).spearmanRho =
      1 - (1 / 4 : ℝ) ^ n * (1 - C.spearmanRho) := by
  induction n with
  | zero => simp [dyadicBlocks]
  | succ n ih =>
    rw [dyadicBlocks, Copula.spearmanRho_ordinalSum, ih]
    norm_num [Copula.unitHalf, pow_succ]
    ring

theorem dyadicBlocks_tau (n : ℕ) (C : Copula 2) :
    (dyadicBlocks n C).kendallTau =
      1 - (1 / 2 : ℝ) ^ n * (1 - C.kendallTau) := by
  induction n with
  | zero => simp [dyadicBlocks]
  | succ n ih =>
    rw [dyadicBlocks, Copula.kendallTau_ordinalSum, ih]
    norm_num [Copula.unitHalf, pow_succ]
    ring

/-- Proposition 3.3(i)-(ii), restricted to diagonal dyadic checkerboards. -/
theorem checkerboard_rho_tau (n : ℕ) :
    (dyadicBlocks n (Copula.independence 2)).spearmanRho = 1 - (1 / 4 : ℝ) ^ n ∧
    (dyadicBlocks n (Copula.independence 2)).kendallTau = 1 - (1 / 2 : ℝ) ^ n := by
  simp [dyadicBlocks_rho, dyadicBlocks_tau]

/-- The check-min corrections are 1/N^2 for rho and 1/N for tau, N=2^n. -/
theorem checkMin_corrections (n : ℕ) :
    (dyadicBlocks n (Copula.comonotonic 2)).spearmanRho =
      (dyadicBlocks n (Copula.independence 2)).spearmanRho + (1 / 4 : ℝ) ^ n ∧
    (dyadicBlocks n (Copula.comonotonic 2)).kendallTau =
      (dyadicBlocks n (Copula.independence 2)).kendallTau + (1 / 2 : ℝ) ^ n := by
  simp [dyadicBlocks_rho, dyadicBlocks_tau]

/-- The check-w corrections have the opposite signs on these same grids. -/
theorem checkW_corrections (n : ℕ) :
    (dyadicBlocks n Copula.countermonotonic).spearmanRho =
      (dyadicBlocks n (Copula.independence 2)).spearmanRho - (1 / 4 : ℝ) ^ n ∧
    (dyadicBlocks n Copula.countermonotonic).kendallTau =
      (dyadicBlocks n (Copula.independence 2)).kendallTau - (1 / 2 : ℝ) ^ n := by
  simp only [dyadicBlocks_rho, dyadicBlocks_tau, Copula.spearmanRho_countermonotonic,
    Copula.spearmanRho_independence, Copula.kendallTau_countermonotonic,
    Copula.kendallTau_independence]
  constructor <;> ring

end Papers.Rockel2025Approximation
