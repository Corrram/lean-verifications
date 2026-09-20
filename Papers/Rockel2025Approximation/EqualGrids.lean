import Papers.Rockel2025Approximation.Definitions
import Verification.EqualBlocks
import Copula.TailDependence.Examples

/-! # Proposition 3.3 on all equal diagonal grids

Here N=n+1 is any positive integer and Delta=I_N/N. This removes the dyadic
restriction for rho and tau and adds deterministic xi and tail values.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2025Approximation

noncomputable def equalGrid (n : ℕ) (C : Copula 2) : Copula 2 :=
  Verification.equalBlocks n C

theorem equalGrid_cdf (n : ℕ) (C : Copula 2) (u v : I) :
    (equalGrid (n + 1) C).cdf ![u, v] =
      (1 / ((n : ℝ) + 2)) * C.cdf
        ![Copula.OrdinalSum.lowerCoord (Verification.equalSplit n) u,
          Copula.OrdinalSum.lowerCoord (Verification.equalSplit n) v] +
      (1 - 1 / ((n : ℝ) + 2)) * (equalGrid n C).cdf
        ![Copula.OrdinalSum.upperCoord (Verification.equalSplit n) u,
          Copula.OrdinalSum.upperCoord (Verification.equalSplit n) v] := by
  rw [equalGrid, Verification.equalBlocks, Copula.cdf_ordinalSum]
  rfl

theorem equalGrid_rho_tau (n : ℕ) (C : Copula 2) :
    (equalGrid n C).spearmanRho = 1 - (1 - C.spearmanRho) / ((n : ℝ) + 1) ^ 2 ∧
    (equalGrid n C).kendallTau = 1 - (1 - C.kendallTau) / ((n : ℝ) + 1) :=
  ⟨Verification.equalBlocks_rho n C, Verification.equalBlocks_tau n C⟩

theorem equal_checkerboard_rho_tau (n : ℕ) :
    (equalGrid n (Copula.independence 2)).spearmanRho = 1 - 1 / ((n : ℝ) + 1) ^ 2 ∧
    (equalGrid n (Copula.independence 2)).kendallTau = 1 - 1 / ((n : ℝ) + 1) := by
  simpa using equalGrid_rho_tau n (Copula.independence 2)

theorem equal_checkMin_coefficients (n : ℕ) :
    (equalGrid n (Copula.comonotonic 2)).spearmanRho =
      (equalGrid n (Copula.independence 2)).spearmanRho + 1 / ((n : ℝ) + 1) ^ 2 ∧
    (equalGrid n (Copula.comonotonic 2)).kendallTau =
      (equalGrid n (Copula.independence 2)).kendallTau + 1 / ((n : ℝ) + 1) ∧
    (equalGrid n (Copula.comonotonic 2)).chatterjeeXi = 1 := by
  refine ⟨?_, ?_, (Verification.functional_comonotonic.equalBlocks n).xi_eq_one⟩
  · simp [equalGrid, Verification.equalBlocks_rho]
  · simp [equalGrid, Verification.equalBlocks_tau]

theorem equal_checkW_coefficients (n : ℕ) :
    (equalGrid n Copula.countermonotonic).spearmanRho =
      (equalGrid n (Copula.independence 2)).spearmanRho - 1 / ((n : ℝ) + 1) ^ 2 ∧
    (equalGrid n Copula.countermonotonic).kendallTau =
      (equalGrid n (Copula.independence 2)).kendallTau - 1 / ((n : ℝ) + 1) ∧
    (equalGrid n Copula.countermonotonic).chatterjeeXi = 1 := by
  refine ⟨?_, ?_, (Verification.functional_countermonotonic.equalBlocks n).xi_eq_one⟩
  · simp only [equalGrid, Verification.equalBlocks_rho, Copula.spearmanRho_countermonotonic,
      Copula.spearmanRho_independence]
    ring
  · simp only [equalGrid, Verification.equalBlocks_tau, Copula.kendallTau_countermonotonic,
      Copula.kendallTau_independence]
    ring

theorem equal_checkerboard_tails (n : ℕ) :
    (equalGrid n (Copula.independence 2)).HasLowerTailDependence 0 ∧
    (equalGrid n (Copula.independence 2)).HasUpperTailDependence 0 :=
  ⟨Verification.equalBlocks_lower_tail _ Copula.hasLowerTailDependence_independence n,
    Verification.equalBlocks_upper_tail _ Copula.hasUpperTailDependence_independence n⟩

theorem equal_checkMin_tails (n : ℕ) :
    (equalGrid n (Copula.comonotonic 2)).HasLowerTailDependence 1 ∧
    (equalGrid n (Copula.comonotonic 2)).HasUpperTailDependence 1 :=
  ⟨Verification.equalBlocks_lower_tail _ Copula.hasLowerTailDependence_comonotonic n,
    Verification.equalBlocks_upper_tail _ Copula.hasUpperTailDependence_comonotonic n⟩

theorem equal_checkW_tails (n : ℕ) :
    (equalGrid n Copula.countermonotonic).HasLowerTailDependence 0 ∧
    (equalGrid n Copula.countermonotonic).HasUpperTailDependence 0 :=
  ⟨Verification.equalBlocks_lower_tail _ Copula.hasLowerTailDependence_countermonotonic n,
    Verification.equalBlocks_upper_tail _ Copula.hasUpperTailDependence_countermonotonic n⟩

end Papers.Rockel2025Approximation
