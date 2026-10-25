import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Functions given by a value and a piecewise derivative

An article may define a function by its value at one point and its derivative,
given piecewise on open intervals (`φ(a) = 0`, `φ'(x) = …` for `0 < x < a` and
for `a < x < 1`). Proofread reads this as `φ(x) = ∫_a^x φ'`. The two lemmas here
evaluate such integrals one piece at a time: on a piece, the integrand agrees
with a continuous function, which is the derivative of a known antiderivative. -/

namespace Papers.Common
open MeasureTheory Set

/-- A function that agrees on `(a,b)` with a function continuous on `[a,b]` is
integrable between `a` and `b`. -/
theorem intervalIntegrable_piece {g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hh : ContinuousOn h (Icc a b))
    (heq : EqOn g h (Ioo a b)) : IntervalIntegrable g volume a b :=
  (hh.intervalIntegrable_of_Icc hab).congr_uIoo (by rw [uIoo_of_le hab]; exact heq.symm)

/-- The fundamental theorem of calculus on one piece. -/
theorem integral_piece {F g h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hF : ContinuousOn F (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (h x) x) (hh : ContinuousOn h (Icc a b))
    (heq : EqOn g h (Ioo a b)) : ∫ x in a..b, g x = F b - F a := by
  rw [intervalIntegral.integral_congr_uIoo (by rw [uIoo_of_le hab]; exact heq)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd (hh.intervalIntegrable_of_Icc hab)

/-- Integrability across two adjacent pieces. -/
theorem intervalIntegrable_two_pieces {g h₁ h₂ : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hc₁ : ContinuousOn h₁ (Icc a m)) (he₁ : EqOn g h₁ (Ioo a m))
    (hc₂ : ContinuousOn h₂ (Icc m b)) (he₂ : EqOn g h₂ (Ioo m b)) : IntervalIntegrable g volume a b :=
  (intervalIntegrable_piece ham hc₁ he₁).trans (intervalIntegrable_piece hmb hc₂ he₂)

/-- The fundamental theorem of calculus across two adjacent pieces. -/
theorem integral_two_pieces {F g h₁ h₂ : ℝ → ℝ} {a m b : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hF : ContinuousOn F (Icc a b))
    (hd₁ : ∀ x ∈ Ioo a m, HasDerivAt F (h₁ x) x) (hc₁ : ContinuousOn h₁ (Icc a m)) (he₁ : EqOn g h₁ (Ioo a m))
    (hd₂ : ∀ x ∈ Ioo m b, HasDerivAt F (h₂ x) x) (hc₂ : ContinuousOn h₂ (Icc m b)) (he₂ : EqOn g h₂ (Ioo m b)) :
    ∫ x in a..b, g x = F b - F a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_piece ham hc₁ he₁)
    (intervalIntegrable_piece hmb hc₂ he₂),
    integral_piece ham (hF.mono (Icc_subset_Icc le_rfl hmb)) hd₁ hc₁ he₁,
    integral_piece hmb (hF.mono (Icc_subset_Icc ham le_rfl)) hd₂ hc₂ he₂]
  ring

/-- Integrability across three adjacent pieces. -/
theorem intervalIntegrable_three_pieces {g h₁ h₂ h₃ : ℝ → ℝ} {a m n b : ℝ} (ham : a ≤ m) (hmn : m ≤ n)
    (hnb : n ≤ b) (hc₁ : ContinuousOn h₁ (Icc a m)) (he₁ : EqOn g h₁ (Ioo a m))
    (hc₂ : ContinuousOn h₂ (Icc m n)) (he₂ : EqOn g h₂ (Ioo m n))
    (hc₃ : ContinuousOn h₃ (Icc n b)) (he₃ : EqOn g h₃ (Ioo n b)) : IntervalIntegrable g volume a b :=
  ((intervalIntegrable_piece ham hc₁ he₁).trans (intervalIntegrable_piece hmn hc₂ he₂)).trans
    (intervalIntegrable_piece hnb hc₃ he₃)

/-- The fundamental theorem of calculus across three adjacent pieces. -/
theorem integral_three_pieces {F g h₁ h₂ h₃ : ℝ → ℝ} {a m n b : ℝ} (ham : a ≤ m) (hmn : m ≤ n)
    (hnb : n ≤ b) (hF : ContinuousOn F (Icc a b))
    (hd₁ : ∀ x ∈ Ioo a m, HasDerivAt F (h₁ x) x) (hc₁ : ContinuousOn h₁ (Icc a m)) (he₁ : EqOn g h₁ (Ioo a m))
    (hd₂ : ∀ x ∈ Ioo m n, HasDerivAt F (h₂ x) x) (hc₂ : ContinuousOn h₂ (Icc m n)) (he₂ : EqOn g h₂ (Ioo m n))
    (hd₃ : ∀ x ∈ Ioo n b, HasDerivAt F (h₃ x) x) (hc₃ : ContinuousOn h₃ (Icc n b)) (he₃ : EqOn g h₃ (Ioo n b)) :
    ∫ x in a..b, g x = F b - F a := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_piece ham hc₁ he₁).trans (intervalIntegrable_piece hmn hc₂ he₂))
    (intervalIntegrable_piece hnb hc₃ he₃),
    integral_two_pieces ham hmn (hF.mono (Icc_subset_Icc le_rfl hnb)) hd₁ hc₁ he₁ hd₂ hc₂ he₂,
    integral_piece hnb (hF.mono (Icc_subset_Icc (ham.trans hmn) le_rfl)) hd₃ hc₃ he₃]
  ring

end Papers.Common
