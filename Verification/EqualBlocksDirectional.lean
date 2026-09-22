import Verification.EqualBlocks
import Verification.OrdinalConditionalRank

/-! # Directional coefficients for equal diagonal blocks -/

open ProbabilityTheory
open scoped unitInterval

namespace Verification

theorem equalBlocks_xi (n : ℕ) (C : Copula 2) :
    (equalBlocks n C).chatterjeeXi = 1-(1-C.chatterjeeXi)/((n : ℝ)+1) := by
  induction n with
  | zero => simp [equalBlocks]
  | succ n ih =>
    rw [equalBlocks,chatterjeeXi_ordinalSum,ih]
    simp only [equalSplit,Nat.cast_add,Nat.cast_one]
    have h1 : (n : ℝ)+1 ≠ 0 := by positivity
    have h2 : (n : ℝ)+2 ≠ 0 := by positivity
    rw [show (n : ℝ)+1+1=n+2 by ring]
    field_simp
    ring

theorem equalBlocks_correlationRatio (n : ℕ) (C : Copula 2) :
    correlationRatio (equalBlocks n C) = 1-(1-correlationRatio C)/((n : ℝ)+1)^2 := by
  induction n with
  | zero => simp [equalBlocks]
  | succ n ih =>
    rw [equalBlocks,correlationRatio_ordinalSum,ih]
    simp only [equalSplit,Nat.cast_add,Nat.cast_one]
    have h1 : (n : ℝ)+1 ≠ 0 := by positivity
    have h2 : (n : ℝ)+2 ≠ 0 := by positivity
    rw [show (n : ℝ)+1+1=n+2 by ring]
    field_simp
    ring

end Verification
