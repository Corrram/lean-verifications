import Papers.Rockel2026ExactBlest.ExactBlestBeta

/-! Exact beta--Blest region in exact-blest-regions.tex, without uniqueness.
All certificate identities and nonnegative Bernstein coefficients are kernel checked. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

def paramPhi0 (_q x : ℝ) : ℝ := 2 * x ^ 3 / 3
def paramPhi1 (q x : ℝ) : ℝ := 2 * x ^ 3 / 3 + (1 / 2 - q) * x ^ 2 + q ^ 3 - q ^ 2 / 2
def paramPhi2 (q x : ℝ) : ℝ := 2 * x ^ 3 / 3 + (q - 1 / 2) * x ^ 2 + 1 / 24 - q ^ 3 / 3
def paramPhi3 (q x : ℝ) : ℝ := 2 * x ^ 3 / 3 + 2 * q ^ 3 / 3 - 5 * q ^ 2 / 2 + 2 * q - 11 / 24
def paramPsi0 (_q z : ℝ) : ℝ := z ^ 3 / 3
def paramPsi1 (q z : ℝ) : ℝ := z ^ 3 / 3 + (1 / 2 - q) * z ^ 2 + (q ^ 2 - q + 1 / 4) * z + q ^ 2 / 2 - q / 4
def paramPsi2 (q z : ℝ) : ℝ := z ^ 3 / 3 + (q - 1 / 2) * z ^ 2 + (q ^ 2 - q + 1 / 4) * z - 2 * q ^ 3 / 3 + q / 4 - 1 / 24
def paramPsi3 (q z : ℝ) : ℝ := z ^ 3 / 3 - 2 * q ^ 3 / 3 - q ^ 2 / 2 + q - 7 / 24

theorem interval_parameter (lo hi x : ℝ) (hx : x ∈ Icc lo hi) :
    ∃ t : I, lo + (hi - lo) * (t : ℝ) = x := by
  exact Verification.exists_unitInterval_eq (by fun_prop)
    (by simpa using hx.1) (by simpa using hx.2)

#assert_standard_axioms Papers.Rockel2026ExactBlest.interval_parameter

theorem beta_param_cell_00 (q x z : ℝ) (_hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc 0 q) (hz : z ∈ Icc 0 q) :
    0 ≤ paramPhi0 q x + paramPsi0 q z - x ^ 2 * z := by
  have he : paramPhi0 q x + paramPsi0 q z - x ^ 2 * z = (x - z) ^ 2 * (2 * x + z) / 3 := by
    unfold paramPhi0 paramPsi0
    ring
  rw [he]
  have hp : 0 ≤ 2 * x + z := by linarith [_hq.1, _hq.2, hx.1, hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_00

theorem beta_param_cell_01 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc 0 q) (hz : z ∈ Icc q (1 / 2)) :
    0 ≤ paramPhi0 q x + paramPsi1 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter 0 q x hx
  obtain ⟨v, hv⟩ := interval_parameter q (1 / 2) z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi0 q x + paramPsi1 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow 0 (1 / 24) (1 / 8) (7 / 24) (v : ℝ)) (bernsteinRow 0 (1 / 24) (1 / 8) (7 / 24) (v : ℝ)) (bernsteinRow 0 (1 / 24) (1 / 8) (7 / 24) (v : ℝ)) (bernsteinRow 0 (1 / 24) (1 / 8) (7 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 (1 / 36) (5 / 72) (1 / 8) (v : ℝ)) (bernsteinRow 0 (1 / 36) (5 / 72) (1 / 8) (v : ℝ)) (bernsteinRow 0 (1 / 36) (5 / 72) (1 / 8) (v : ℝ)) (bernsteinRow 0 (1 / 36) (5 / 72) (1 / 8) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 (1 / 72) (1 / 36) (1 / 24) (v : ℝ)) (bernsteinRow 0 (1 / 72) (1 / 36) (1 / 24) (v : ℝ)) (bernsteinRow 0 (1 / 108) (1 / 54) (1 / 36) (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi0 paramPsi1 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_01

theorem beta_param_cell_02 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc 0 q) (hz : z ∈ Icc (1 / 2) (1 - q)) :
    0 ≤ paramPhi0 q x + paramPsi2 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter 0 q x hx
  obtain ⟨v, hv⟩ := interval_parameter (1 / 2) (1 - q) z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi0 q x + paramPsi2 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow 0 0 0 (1 / 24) (v : ℝ)) (bernsteinRow 0 0 0 (1 / 24) (v : ℝ)) (bernsteinRow 0 0 0 (1 / 24) (v : ℝ)) (bernsteinRow 0 0 0 (1 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 (1 / 72) (1 / 24) (v : ℝ)) (bernsteinRow 0 0 (1 / 72) (1 / 24) (v : ℝ)) (bernsteinRow 0 0 (1 / 72) (1 / 24) (v : ℝ)) (bernsteinRow 0 0 (1 / 72) (1 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 18) (5 / 72) (1 / 12) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 18) (5 / 72) (1 / 12) (v : ℝ)) (bernsteinRow (1 / 36) (1 / 27) (5 / 108) (1 / 18) (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi0 paramPsi2 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_02

theorem beta_param_cell_03 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc 0 q) (hz : z ∈ Icc (1 - q) 1) :
    0 ≤ paramPhi0 q x + paramPsi3 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter 0 q x hx
  obtain ⟨v, hv⟩ := interval_parameter (1 - q) 1 z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi0 q x + paramPsi3 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (7 / 72) (11 / 72) (5 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (7 / 72) (11 / 72) (5 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (7 / 72) (11 / 72) (5 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (7 / 72) (11 / 72) (5 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 12) (5 / 36) (2 / 9) (1 / 3) (v : ℝ)) (bernsteinRow (1 / 12) (5 / 36) (2 / 9) (1 / 3) (v : ℝ)) (bernsteinRow (1 / 18) (1 / 9) (7 / 36) (11 / 36) (v : ℝ)) (bernsteinRow 0 (1 / 18) (5 / 36) (1 / 4) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 12) (1 / 6) (1 / 3) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 12) (1 / 6) (1 / 3) (v : ℝ)) (bernsteinRow 0 (1 / 36) (7 / 72) (1 / 4) (v : ℝ)) (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi0 paramPsi3 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_03

theorem beta_param_cell_10 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc q (1 / 2)) (hz : z ∈ Icc 0 q) :
    0 ≤ paramPhi1 q x + paramPsi0 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter q (1 / 2) x hx
  obtain ⟨v, hv⟩ := interval_parameter 0 q z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi1 q x + paramPsi0 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 36) (1 / 36) (1 / 36) (1 / 36) (v : ℝ)) (bernsteinRow (1 / 12) (17 / 216) (2 / 27) (5 / 72) (v : ℝ)) (bernsteinRow (1 / 6) (11 / 72) (5 / 36) (1 / 8) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 36) (1 / 54) (1 / 108) 0 (v : ℝ)) (bernsteinRow (1 / 18) (1 / 27) (1 / 54) 0 (v : ℝ)) (bernsteinRow (1 / 12) (1 / 18) (1 / 36) 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi1 paramPsi0 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_10

theorem beta_param_cell_11 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc q (1 / 2)) (hz : z ∈ Icc q (1 / 2)) :
    0 ≤ paramPhi1 q x + paramPsi1 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter q (1 / 2) x hx
  obtain ⟨v, hv⟩ := interval_parameter q (1 / 2) z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi1 q x + paramPsi1 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow 0 (1 / 24) (1 / 8) (7 / 24) (v : ℝ)) (bernsteinRow 0 (1 / 24) (1 / 8) (7 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (5 / 72) (5 / 36) (7 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (1 / 4) (3 / 8) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 (1 / 36) (5 / 72) (1 / 8) (v : ℝ)) (bernsteinRow (1 / 36) (5 / 108) (17 / 216) (1 / 8) (v : ℝ)) (bernsteinRow (5 / 72) (17 / 216) (11 / 108) (5 / 36) (v : ℝ)) (bernsteinRow (1 / 8) (1 / 8) (5 / 36) (1 / 6) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi1 paramPsi1 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_11

theorem beta_param_cell_12 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc q (1 / 2)) (hz : z ∈ Icc (1 / 2) (1 - q)) :
    0 ≤ paramPhi1 q x + paramPsi2 q z - x ^ 2 * z := by
  have he : paramPhi1 q x + paramPsi2 q z - x ^ 2 * z = (x - z + (1 / 2 - q)) ^ 2 * (2 * x + z - (1 / 2 - q)) / 3 := by
    unfold paramPhi1 paramPsi2
    ring
  rw [he]
  have hp : 0 ≤ 2 * x + z - (1 / 2 - q) := by linarith [hq.1, hq.2, hx.1, hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_12

theorem beta_param_cell_13 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc q (1 / 2)) (hz : z ∈ Icc (1 - q) 1) :
    0 ≤ paramPhi1 q x + paramPsi3 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter q (1 / 2) x hx
  obtain ⟨v, hv⟩ := interval_parameter (1 - q) 1 z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi1 q x + paramPsi3 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (7 / 72) (11 / 72) (5 / 24) (v : ℝ)) (bernsteinRow (1 / 72) (5 / 72) (1 / 8) (13 / 72) (v : ℝ)) (bernsteinRow 0 (11 / 216) (11 / 108) (11 / 72) (v : ℝ)) (bernsteinRow 0 (1 / 24) (1 / 12) (1 / 8) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 (1 / 18) (5 / 36) (1 / 4) (v : ℝ)) (bernsteinRow 0 (5 / 108) (13 / 108) (2 / 9) (v : ℝ)) (bernsteinRow 0 (1 / 27) (11 / 108) (7 / 36) (v : ℝ)) (bernsteinRow 0 (1 / 36) (1 / 12) (1 / 6) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi1 paramPsi3 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_13

theorem beta_param_cell_20 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 / 2) (1 - q)) (hz : z ∈ Icc 0 q) :
    0 ≤ paramPhi2 q x + paramPsi0 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter (1 / 2) (1 - q) x hx
  obtain ⟨v, hv⟩ := interval_parameter 0 q z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi2 q x + paramPsi0 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 36) (1 / 72) 0 (v : ℝ)) (bernsteinRow (5 / 72) (5 / 108) (5 / 216) 0 (v : ℝ)) (bernsteinRow (1 / 8) (19 / 216) (11 / 216) (1 / 72) (v : ℝ)) (bernsteinRow (5 / 24) (11 / 72) (7 / 72) (1 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 12) (1 / 18) (1 / 36) 0 (v : ℝ)) (bernsteinRow (1 / 9) (2 / 27) (1 / 27) 0 (v : ℝ)) (bernsteinRow (5 / 36) (5 / 54) (5 / 108) 0 (v : ℝ)) (bernsteinRow (1 / 6) (1 / 9) (1 / 18) 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi2 paramPsi0 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_20

theorem beta_param_cell_21 (q x z : ℝ) (_hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 / 2) (1 - q)) (hz : z ∈ Icc q (1 / 2)) :
    0 ≤ paramPhi2 q x + paramPsi1 q z - x ^ 2 * z := by
  have he : paramPhi2 q x + paramPsi1 q z - x ^ 2 * z = (x - z - (1 / 2 - q)) ^ 2 * (2 * x + z + (1 / 2 - q)) / 3 := by
    unfold paramPhi2 paramPsi1
    ring
  rw [he]
  have hp : 0 ≤ 2 * x + z + (1 / 2 - q) := by linarith [_hq.1, _hq.2, hx.1, hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_21

theorem beta_param_cell_22 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 / 2) (1 - q)) (hz : z ∈ Icc (1 / 2) (1 - q)) :
    0 ≤ paramPhi2 q x + paramPsi2 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 := by
  obtain ⟨u, hu⟩ := interval_parameter (1 / 2) (1 - q) x hx
  obtain ⟨v, hv⟩ := interval_parameter (1 / 2) (1 - q) z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi2 q x + paramPsi2 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 = bernsteinRow
      (bernsteinRow (bernsteinRow (5 / 8) (7 / 12) (13 / 24) (13 / 24) (v : ℝ)) (bernsteinRow (13 / 24) (17 / 36) (29 / 72) (3 / 8) (v : ℝ)) (bernsteinRow (11 / 24) (25 / 72) (17 / 72) (1 / 6) (v : ℝ)) (bernsteinRow (11 / 24) (7 / 24) (1 / 8) 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 6) (5 / 36) (1 / 8) (1 / 8) (v : ℝ)) (bernsteinRow (5 / 36) (11 / 108) (17 / 216) (5 / 72) (v : ℝ)) (bernsteinRow (1 / 8) (17 / 216) (5 / 108) (1 / 36) (v : ℝ)) (bernsteinRow (1 / 8) (5 / 72) (1 / 36) 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi2 paramPsi2 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_22

theorem beta_param_cell_23 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 / 2) (1 - q)) (hz : z ∈ Icc (1 - q) 1) :
    0 ≤ paramPhi2 q x + paramPsi3 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 := by
  obtain ⟨u, hu⟩ := interval_parameter (1 / 2) (1 - q) x hx
  obtain ⟨v, hv⟩ := interval_parameter (1 - q) 1 z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi2 q x + paramPsi3 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 = bernsteinRow
      (bernsteinRow (bernsteinRow (13 / 24) (13 / 24) (13 / 24) (13 / 24) (v : ℝ)) (bernsteinRow (3 / 8) (3 / 8) (3 / 8) (3 / 8) (v : ℝ)) (bernsteinRow (1 / 6) (1 / 6) (1 / 6) (1 / 6) (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 8) (1 / 6) (5 / 24) (1 / 4) (v : ℝ)) (bernsteinRow (5 / 72) (11 / 108) (29 / 216) (1 / 6) (v : ℝ)) (bernsteinRow (1 / 36) (5 / 108) (7 / 108) (1 / 12) (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 (1 / 36) (1 / 12) (1 / 6) (v : ℝ)) (bernsteinRow 0 (1 / 54) (7 / 108) (5 / 36) (v : ℝ)) (bernsteinRow 0 (1 / 108) (5 / 108) (1 / 9) (v : ℝ)) (bernsteinRow 0 0 (1 / 36) (1 / 12) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (bernsteinRow 0 0 (1 / 24) (1 / 6) (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi2 paramPsi3 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_23

theorem beta_param_cell_30 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 - q) 1) (hz : z ∈ Icc 0 q) :
    0 ≤ paramPhi3 q x + paramPsi0 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter (1 - q) 1 x hx
  obtain ⟨v, hv⟩ := interval_parameter 0 q z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi3 q x + paramPsi0 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (5 / 24) (11 / 72) (7 / 72) (1 / 24) (v : ℝ)) (bernsteinRow (23 / 72) (19 / 72) (5 / 24) (11 / 72) (v : ℝ)) (bernsteinRow (31 / 72) (3 / 8) (23 / 72) (19 / 72) (v : ℝ)) (bernsteinRow (13 / 24) (35 / 72) (31 / 72) (3 / 8) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 6) (1 / 9) (1 / 18) 0 (v : ℝ)) (bernsteinRow (5 / 18) (11 / 54) (7 / 54) (1 / 18) (v : ℝ)) (bernsteinRow (4 / 9) (19 / 54) (7 / 27) (1 / 6) (v : ℝ)) (bernsteinRow (2 / 3) (5 / 9) (4 / 9) (1 / 3) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 12) (1 / 24) 0 0 (v : ℝ)) (bernsteinRow (1 / 6) (7 / 72) (1 / 36) 0 (v : ℝ)) (bernsteinRow (1 / 3) (2 / 9) (1 / 9) (1 / 24) (v : ℝ)) (bernsteinRow (2 / 3) (1 / 2) (1 / 3) (5 / 24) (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi3 paramPsi0 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_30

theorem beta_param_cell_31 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 - q) 1) (hz : z ∈ Icc q (1 / 2)) :
    0 ≤ paramPhi3 q x + paramPsi1 q z - x ^ 2 * z := by
  obtain ⟨u, hu⟩ := interval_parameter (1 - q) 1 x hx
  obtain ⟨v, hv⟩ := interval_parameter q (1 / 2) z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi3 q x + paramPsi1 q z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (bernsteinRow (5 / 24) (1 / 12) 0 0 (v : ℝ)) (bernsteinRow (5 / 24) (1 / 12) 0 0 (v : ℝ)) (bernsteinRow (5 / 24) (1 / 12) 0 0 (v : ℝ)) (bernsteinRow (5 / 24) (1 / 12) 0 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 24) (1 / 72) 0 0 (v : ℝ)) (bernsteinRow (11 / 72) (23 / 216) (2 / 27) (1 / 18) (v : ℝ)) (bernsteinRow (19 / 72) (43 / 216) (4 / 27) (1 / 9) (v : ℝ)) (bernsteinRow (3 / 8) (7 / 24) (2 / 9) (1 / 6) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 18) (5 / 108) (1 / 27) (1 / 36) (v : ℝ)) (bernsteinRow (1 / 6) (31 / 216) (13 / 108) (7 / 72) (v : ℝ)) (bernsteinRow (1 / 3) (7 / 24) (1 / 4) (5 / 24) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi3 paramPsi1 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_31

theorem beta_param_cell_32 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 - q) 1) (hz : z ∈ Icc (1 / 2) (1 - q)) :
    0 ≤ paramPhi3 q x + paramPsi2 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 := by
  obtain ⟨u, hu⟩ := interval_parameter (1 - q) 1 x hx
  obtain ⟨v, hv⟩ := interval_parameter (1 / 2) (1 - q) z hz
  have hr : 2 * q ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have he : paramPhi3 q x + paramPsi2 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 = bernsteinRow
      (bernsteinRow (bernsteinRow (11 / 24) (7 / 24) (1 / 8) 0 (v : ℝ)) (bernsteinRow (11 / 24) (7 / 24) (1 / 8) 0 (v : ℝ)) (bernsteinRow (11 / 24) (7 / 24) (1 / 8) 0 (v : ℝ)) (bernsteinRow (11 / 24) (7 / 24) (1 / 8) 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow (1 / 8) (5 / 72) (1 / 36) 0 (v : ℝ)) (bernsteinRow (13 / 72) (23 / 216) (5 / 108) 0 (v : ℝ)) (bernsteinRow (17 / 72) (31 / 216) (7 / 108) 0 (v : ℝ)) (bernsteinRow (7 / 24) (13 / 72) (1 / 12) 0 (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 36) (1 / 54) (1 / 108) 0 (v : ℝ)) (bernsteinRow (7 / 72) (2 / 27) (11 / 216) (1 / 36) (v : ℝ)) (bernsteinRow (5 / 24) (1 / 6) (1 / 8) (1 / 12) (v : ℝ)) (u : ℝ))
      (bernsteinRow (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow 0 0 0 0 (v : ℝ)) (bernsteinRow (1 / 24) (1 / 24) (1 / 24) (1 / 24) (v : ℝ)) (bernsteinRow (5 / 24) (5 / 24) (5 / 24) (5 / 24) (v : ℝ)) (u : ℝ))
      (2 * q) := by
    rw [← hu, ← hv]
    unfold paramPhi3 paramPsi2 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hr <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ u.property <;>
      (apply bernsteinRow_nonneg _ _ _ _ _ v.property <;> norm_num))
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_32

theorem beta_param_cell_33 (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2))
    (hx : x ∈ Icc (1 - q) 1) (hz : z ∈ Icc (1 - q) 1) :
    0 ≤ paramPhi3 q x + paramPsi3 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 := by
  have he : paramPhi3 q x + paramPsi3 q z - x ^ 2 * z + 3 * (1 / 2 - q) ^ 2 = (x - z) ^ 2 * (2 * x + z) / 3 := by
    unfold paramPhi3 paramPsi3
    ring
  rw [he]
  have hp : 0 ≤ 2 * x + z := by linarith [hq.1, hq.2, hx.1, hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_cell_33

def paramPieces (q : ℝ) (f0 f1 f2 f3 : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ q then f0 x else if x ≤ 1 / 2 then f1 x else if x ≤ 1 - q then f2 x else f3 x
def paramPhi (q : ℝ) : ℝ → ℝ := paramPieces q (paramPhi0 q) (paramPhi1 q) (paramPhi2 q) (paramPhi3 q)
def paramPsi (q : ℝ) : ℝ → ℝ := paramPieces q (paramPsi0 q) (paramPsi1 q) (paramPsi2 q) (paramPsi3 q)

theorem paramPieces_decomposition (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (f0 f1 f2 f3 : ℝ → ℝ) :
    paramPieces q f0 f1 f2 f3 = fun x => f3 x + cutValue (fun x => f2 x - f3 x) (1 - q) x +
      cutValue (fun x => f1 x - f2 x) (1 / 2) x + cutValue (fun x => f0 x - f1 x) q x := by
  funext x
  unfold paramPieces cutValue
  split_ifs <;> linarith [hq.2]

theorem integral_paramPieces (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (f0 f1 f2 f3 : ℝ → ℝ)
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) :
    (∫ u : I, paramPieces q f0 f1 f2 f3 u) = (∫ u : I, f3 u) +
      (∫ x in (0 : ℝ)..(1 - q), f2 x - f3 x) +
      (∫ x in (0 : ℝ)..(1 / 2), f1 x - f2 x) + (∫ x in (0 : ℝ)..q, f0 x - f1 x) := by
  have hi3 : Integrable (fun u : I => f3 u) := Copula.integrable_continuous_unit _ (by fun_prop)
  have hi2 := integrable_cutValue (fun x => f2 x - f3 x) (h2.sub h3) (1 - q)
  have hi1 := integrable_cutValue (fun x => f1 x - f2 x) (h1.sub h2) (1 / 2)
  have hi0 := integrable_cutValue (fun x => f0 x - f1 x) (h0.sub h1) q
  have ha0 := integral_add ((hi3.add hi2).add hi1) hi0
  have ha1 := integral_add (hi3.add hi2) hi1
  have ha2 := integral_add hi3 hi2
  simp only [Pi.add_apply] at ha0 ha1 ha2
  rw [paramPieces_decomposition q hq]
  dsimp only
  rw [ha0, ha1, ha2, integral_cutValue _ _ ⟨by linarith [hq.2], by linarith [hq.1]⟩,
    integral_cutValue _ _ (by norm_num), integral_cutValue _ _ ⟨hq.1, by linarith [hq.2]⟩]

theorem integrable_paramPieces (C : Copula 2) (i : Fin 2) (q : ℝ) (f0 f1 f2 f3 : ℝ → ℝ)
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) :
    Integrable (fun x => paramPieces q f0 f1 f2 f3 (x i)) C.toMeasure := by
  classical
  have hf (f : ℝ → ℝ) (hf : Continuous f) : Integrable (fun x : Fin 2 → I => f (x i)) C.toMeasure :=
    Copula.integrable_continuous_cube _ (by fun_prop)
  have hm (t : ℝ) : MeasurableSet {x : Fin 2 → I | (x i : ℝ) ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  exact Integrable.piecewise (hm _) (hf f0 h0).integrableOn
    (Integrable.piecewise (hm _) (hf f1 h1).integrableOn
      (Integrable.piecewise (hm _) (hf f2 h2).integrableOn (hf f3 h3).integrableOn).integrableOn).integrableOn

theorem measurable_paramPieces (q : ℝ) (f0 f1 f2 f3 : ℝ → ℝ)
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) :
    Measurable (fun u : I => paramPieces q f0 f1 f2 f3 u) := by
  have hf (f : ℝ → ℝ) (hf : Continuous f) : Measurable (fun u : I => f u) := by fun_prop
  have hm (t : ℝ) : MeasurableSet {u : I | (u : ℝ) ≤ t} :=
    measurableSet_le measurable_subtype_coe measurable_const
  exact (hf f0 h0).ite (hm _) ((hf f1 h1).ite (hm _) ((hf f2 h2).ite (hm _) (hf f3 h3)))

#assert_standard_axioms Papers.Rockel2026ExactBlest.paramPieces_decomposition
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_paramPieces
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_paramPieces
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_paramPieces

theorem beta_param_dual (q x z : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    x ^ 2 * z - 3 * (1 / 2 - q) ^ 2 * (if 1 / 2 < x ∧ 1 / 2 < z then (1 : ℝ) else 0) ≤ paramPhi q x + paramPsi q z := by
  by_cases hx0 : x ≤ q
  ·
    by_cases hz0 : z ≤ q
    ·
      have hc := beta_param_cell_00 q x z hq
        (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
        (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
      have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
        rintro ⟨hqx, hqz⟩
        linarith [hq.1, hq.2]
      simp only [paramPhi, paramPsi, paramPieces, ite_eq_left hx0, ite_eq_left hz0, ite_eq_right hh]
      linarith [hq.1, hq.2]
    ·
      by_cases hz1 : z ≤ (1 / 2)
      ·
        have hc := beta_param_cell_01 q x z hq
          (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
          (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
        have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
          rintro ⟨hqx, hqz⟩
          linarith [hq.1, hq.2]
        simp only [paramPhi, paramPsi, paramPieces, ite_eq_left hx0, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hh]
        linarith [hq.1, hq.2]
      ·
        by_cases hz2 : z ≤ (1 - q)
        ·
          have hc := beta_param_cell_02 q x z hq
            (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
            (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
          have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith [hq.1, hq.2]
          simp only [paramPhi, paramPsi, paramPieces, ite_eq_left hx0, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_right hh]
          linarith [hq.1, hq.2]
        ·
          have hc := beta_param_cell_03 q x z hq
            (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
            (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
          have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith [hq.1, hq.2]
          simp only [paramPhi, paramPsi, paramPieces, ite_eq_left hx0, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_right hh]
          linarith [hq.1, hq.2]
  ·
    by_cases hx1 : x ≤ (1 / 2)
    ·
      by_cases hz0 : z ≤ q
      ·
        have hc := beta_param_cell_10 q x z hq
          (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
          (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
        have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
          rintro ⟨hqx, hqz⟩
          linarith [hq.1, hq.2]
        simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_left hx1, ite_eq_left hz0, ite_eq_right hh]
        linarith [hq.1, hq.2]
      ·
        by_cases hz1 : z ≤ (1 / 2)
        ·
          have hc := beta_param_cell_11 q x z hq
            (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
            (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
          have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith [hq.1, hq.2]
          simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_left hx1, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hh]
          linarith [hq.1, hq.2]
        ·
          by_cases hz2 : z ≤ (1 - q)
          ·
            have hc := beta_param_cell_12 q x z hq
              (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
              (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
            have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith [hq.1, hq.2]
            simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_left hx1, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_right hh]
            linarith [hq.1, hq.2]
          ·
            have hc := beta_param_cell_13 q x z hq
              (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
              (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
            have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith [hq.1, hq.2]
            simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_left hx1, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_right hh]
            linarith [hq.1, hq.2]
    ·
      by_cases hx2 : x ≤ (1 - q)
      ·
        by_cases hz0 : z ≤ q
        ·
          have hc := beta_param_cell_20 q x z hq
            (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
            (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
          have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith [hq.1, hq.2]
          simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_left hz0, ite_eq_right hh]
          linarith [hq.1, hq.2]
        ·
          by_cases hz1 : z ≤ (1 / 2)
          ·
            have hc := beta_param_cell_21 q x z hq
              (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
              (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
            have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith [hq.1, hq.2]
            simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hh]
            linarith [hq.1, hq.2]
          ·
            by_cases hz2 : z ≤ (1 - q)
            ·
              have hc := beta_param_cell_22 q x z hq
                (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
                (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
              have hh : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith [hq.1, hq.2]
              simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_left hh]
              linarith [hq.1, hq.2]
            ·
              have hc := beta_param_cell_23 q x z hq
                (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
                (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
              have hh : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith [hq.1, hq.2]
              simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_left hh]
              linarith [hq.1, hq.2]
      ·
        by_cases hz0 : z ≤ q
        ·
          have hc := beta_param_cell_30 q x z hq
            (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
            (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
          have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith [hq.1, hq.2]
          simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_left hz0, ite_eq_right hh]
          linarith [hq.1, hq.2]
        ·
          by_cases hz1 : z ≤ (1 / 2)
          ·
            have hc := beta_param_cell_31 q x z hq
              (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
              (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
            have hh : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith [hq.1, hq.2]
            simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hh]
            linarith [hq.1, hq.2]
          ·
            by_cases hz2 : z ≤ (1 - q)
            ·
              have hc := beta_param_cell_32 q x z hq
                (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
                (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
              have hh : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith [hq.1, hq.2]
              simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_left hh]
              linarith [hq.1, hq.2]
            ·
              have hc := beta_param_cell_33 q x z hq
                (by constructor <;> linarith [hq.1, hq.2, hx.1, hx.2])
                (by constructor <;> linarith [hq.1, hq.2, hz.1, hz.2])
              have hh : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith [hq.1, hq.2]
              simp only [paramPhi, paramPsi, paramPieces, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_left hh]
              linarith [hq.1, hq.2]

#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_param_dual

theorem integral_paramPhi (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    (∫ u : I, paramPhi q u) = -2 * q ^ 3/3 + q ^ 2/4 + q/4 + 1/16 := by
  rw [paramPhi, integral_paramPieces q hq _ _ _ _
    (by unfold paramPhi0; fun_prop) (by unfold paramPhi1; fun_prop)
    (by unfold paramPhi2; fun_prop) (by unfold paramPhi3; fun_prop)]
  have he0 : paramPhi3 q = fun x : ℝ => (2/3) * x ^ 3 + (0) * x ^ 2 + (0) * x + (2 * q ^ 3/3 - 5 * q ^ 2/2 + 2 * q - 11/24) := by
    funext x; unfold paramPhi3; ring
  have he1 : (fun x : ℝ => paramPhi2 q x - paramPhi3 q x) = fun x : ℝ => (0) * x ^ 3 + (q - 1/2) * x ^ 2 + (0) * x + (-q ^ 3 + 5 * q ^ 2/2 - 2 * q + 1/2) := by
    funext x; unfold paramPhi2 paramPhi3; ring
  have he2 : (fun x : ℝ => paramPhi1 q x - paramPhi2 q x) = fun x : ℝ => (0) * x ^ 3 + (1 - 2 * q) * x ^ 2 + (0) * x + (4 * q ^ 3/3 - q ^ 2/2 - 1/24) := by
    funext x; unfold paramPhi1 paramPhi2; ring
  have he3 : (fun x : ℝ => paramPhi0 q x - paramPhi1 q x) = fun x : ℝ => (0) * x ^ 3 + (q - 1/2) * x ^ 2 + (0) * x + (-q ^ 3 + q ^ 2/2) := by
    funext x; unfold paramPhi0 paramPhi1; ring
  rw [he1, he2, he3, he0, Copula.integral_unitInterval (fun x : ℝ => (2/3) * x ^ 3 + (0) * x ^ 2 + (0) * x + (2 * q ^ 3/3 - 5 * q ^ 2/2 + 2 * q - 11/24)),
    integral_poly3, integral_poly3, integral_poly3, integral_poly3]
  ring
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_paramPhi

theorem integral_paramPsi (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    (∫ u : I, paramPsi q u) = -4 * q ^ 3/3 + 5 * q ^ 2/4 - q/4 + 1/16 := by
  rw [paramPsi, integral_paramPieces q hq _ _ _ _
    (by unfold paramPsi0; fun_prop) (by unfold paramPsi1; fun_prop)
    (by unfold paramPsi2; fun_prop) (by unfold paramPsi3; fun_prop)]
  have he0 : paramPsi3 q = fun x : ℝ => (1/3) * x ^ 3 + (0) * x ^ 2 + (0) * x + (-2 * q ^ 3/3 - q ^ 2/2 + q - 7/24) := by
    funext x; unfold paramPsi3; ring
  have he1 : (fun x : ℝ => paramPsi2 q x - paramPsi3 q x) = fun x : ℝ => (0) * x ^ 3 + (q - 1/2) * x ^ 2 + (q ^ 2 - q + 1/4) * x + (q ^ 2/2 - 3 * q/4 + 1/4) := by
    funext x; unfold paramPsi2 paramPsi3; ring
  have he2 : (fun x : ℝ => paramPsi1 q x - paramPsi2 q x) = fun x : ℝ => (0) * x ^ 3 + (1 - 2 * q) * x ^ 2 + (0) * x + (2 * q ^ 3/3 + q ^ 2/2 - q/2 + 1/24) := by
    funext x; unfold paramPsi1 paramPsi2; ring
  have he3 : (fun x : ℝ => paramPsi0 q x - paramPsi1 q x) = fun x : ℝ => (0) * x ^ 3 + (q - 1/2) * x ^ 2 + (-q ^ 2 + q - 1/4) * x + (-q ^ 2/2 + q/4) := by
    funext x; unfold paramPsi0 paramPsi1; ring
  rw [he1, he2, he3, he0, Copula.integral_unitInterval (fun x : ℝ => (1/3) * x ^ 3 + (0) * x ^ 2 + (0) * x + (-2 * q ^ 3/3 - q ^ 2/2 + q - 7/24)),
    integral_poly3, integral_poly3, integral_poly3, integral_poly3]
  ring
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_paramPsi

theorem transport_beta_param_upper (C : Copula 2) (q : ℝ) (hq : q ∈ Icc (0 : ℝ) (1 / 2)) :
    (∫ x, (x 0 : ℝ) ^ 2 * (x 1 : ℝ) - 3 * (1 / 2 - q) ^ 2 * upperQuadrant x ∂C.toMeasure) ≤
      -2 * q ^ 3 + 3 * q ^ 2 / 2 + 1 / 8 := by
  have hp : Integrable (fun x : Fin 2 → I => paramPhi q (x 0)) C.toMeasure :=
    integrable_paramPieces C 0 q _ _ _ _ (by unfold paramPhi0; fun_prop)
      (by unfold paramPhi1; fun_prop) (by unfold paramPhi2; fun_prop) (by unfold paramPhi3; fun_prop)
  have hs : Integrable (fun x : Fin 2 → I => paramPsi q (x 1)) C.toMeasure :=
    integrable_paramPieces C 1 q _ _ _ _ (by unfold paramPsi0; fun_prop)
      (by unfold paramPsi1; fun_prop) (by unfold paramPsi2; fun_prop) (by unfold paramPsi3; fun_prop)
  have hi : Integrable (fun x : Fin 2 → I =>
      (x 0 : ℝ) ^ 2 * (x 1 : ℝ) - 3 * (1 / 2 - q) ^ 2 * upperQuadrant x) C.toMeasure :=
    (Copula.integrable_continuous_cube _ (by fun_prop)).sub
      ((integrable_upperQuadrant C).const_mul _)
  have h := integral_mono hi (hp.add hs)
    (fun x => beta_param_dual q (x 0) (x 1) hq (x 0).property (x 1).property)
  simp only [Pi.add_apply] at h
  rw [integral_add hp hs,
    C.integral_eval 0 (fun u : I => paramPhi q u) (measurable_paramPieces q _ _ _ _
      (by unfold paramPhi0; fun_prop) (by unfold paramPhi1; fun_prop)
      (by unfold paramPhi2; fun_prop) (by unfold paramPhi3; fun_prop)),
    C.integral_eval 1 (fun u : I => paramPsi q u) (measurable_paramPieces q _ _ _ _
      (by unfold paramPsi0; fun_prop) (by unfold paramPsi1; fun_prop)
      (by unfold paramPsi2; fun_prop) (by unfold paramPsi3; fun_prop)),
    integral_paramPhi q hq, integral_paramPsi q hq] at h
  linarith

theorem beta_region_upper (C : Copula 2) : blestNu C ≤ betaUpper C.blomqvistBeta := by
  let q := C.survivalCopula.cdf ![Copula.unitHalf, Copula.unitHalf]
  have hq : q ∈ Icc (0 : ℝ) (1 / 2) := by
    refine ⟨C.survivalCopula.cdf_nonneg _, ?_⟩
    simpa [q, Copula.unitHalf] using
      C.survivalCopula.cdf_le_coord ![Copula.unitHalf, Copula.unitHalf] 0
  have hb : C.blomqvistBeta = 4 * q - 1 := by
    rw [← Copula.blomqvistBeta_survivalCopula C]
    rfl
  have hn := support_moment_survival C 0
  norm_num [cost] at hn
  have ht := transport_beta_param_upper C.survivalCopula q hq
  rw [integral_sub (Copula.integrable_continuous_cube _ (by fun_prop))
    ((integrable_upperQuadrant _).const_mul _), integral_const_mul, integral_upperQuadrant] at ht
  change (∫ x, (x 0 : ℝ) ^ 2 * (x 1 : ℝ) ∂C.survivalCopula.toMeasure) -
    3 * (1 / 2 - q) ^ 2 * q ≤ -2 * q ^ 3 + 3 * q ^ 2 / 2 + 1 / 8 at ht
  rw [hb]
  unfold betaUpper
  nlinarith [ht]

theorem beta_region_lower (C : Copula 2) : betaLower C.blomqvistBeta ≤ blestNu C := by
  have h := beta_region_upper (C.reflect {1})
  rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second] at h
  dsimp [betaUpper, betaLower] at *
  linarith

theorem blest_centered_of_equal (C : Copula 2) (h : blestNu C = C.spearmanRho) (a : I) :
    blestNu (Verification.centeredOrdinal C a) = 1 - (a : ℝ) ^ 3 + (a : ℝ) ^ 3 * C.spearmanRho := by
  unfold Verification.centeredOrdinal
  rw [blest_ordinalSum, blest_ordinalSum, Copula.spearmanRho_comonotonic, blest_comonotonic, h]
  dsimp [Verification.centralMargin, Verification.centralSplit]
  have ha : 1 + (a : ℝ) ≠ 0 := by linarith [a.property.1]
  field_simp
  ring

theorem beta_upper_attained (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧ blestNu C = betaUpper b := by
  let a : I := ⟨(1 - b) / 2, by constructor <;> linarith [hb.1, hb.2]⟩
  refine ⟨Verification.centeredOrdinal halfRotation a, ?_, ?_⟩
  · rw [Verification.centeredOrdinal_beta, halfRotation_values.2.2]
    dsimp [a]
    ring
  · rw [blest_centered_of_equal halfRotation
      (halfRotation_values.1.trans halfRotation_values.2.1.symm), halfRotation_values.2.1]
    dsimp [a, betaUpper]
    ring

theorem beta_lower_attained (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧ blestNu C = betaLower b := by
  obtain ⟨C, hc, hn⟩ := beta_upper_attained (-b) ⟨by linarith [hb.2], by linarith [hb.1]⟩
  refine ⟨C.reflect {1}, ?_, ?_⟩
  · rw [Copula.blomqvistBeta_reflect_second, hc]
    ring
  · rw [blest_reflect_second, hn]
    unfold betaUpper betaLower
    ring

theorem beta_fibre (b n : ℝ) :
    (∃ C : Copula 2, C.blomqvistBeta = b ∧ blestNu C = n) ↔
      b ∈ Icc (-1 : ℝ) 1 ∧ n ∈ Icc (betaLower b) (betaUpper b) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨Copula.blomqvistBeta_mem_Icc C, beta_region_lower C, beta_region_upper C⟩
  · rintro ⟨hb, hn⟩
    obtain ⟨Cu, hbu, hnu⟩ := beta_upper_attained b hb
    obtain ⟨Cl, hbl, hnl⟩ := beta_lower_attained b hb
    have hc : Continuous (fun t : I => blestNu (Cu.mix Cl t)) := by
      simp_rw [blest_mix]
      fun_prop
    obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := n)
      (by simp only [blest_mix]; norm_num; rw [hnl]; exact hn.1)
      (by simp only [blest_mix]; norm_num; rw [hnu]; exact hn.2)
    refine ⟨Cu.mix Cl t, ?_, ht⟩
    rw [Copula.blomqvistBeta_mix, hbu, hbl]
    ring

/-- The full set equality in thm:beta-nu; no boundary-uniqueness claim. -/
theorem beta_nu_region :
    Set.range (fun C : Copula 2 => (C.blomqvistBeta, blestNu C)) =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ∈ Icc (betaLower p.1) (betaUpper p.1)} := by
  ext ⟨b, n⟩
  simpa only [Set.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] using beta_fibre b n

#assert_standard_axioms Papers.Rockel2026ExactBlest.transport_beta_param_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_region_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_region_lower
#assert_standard_axioms Papers.Rockel2026ExactBlest.blest_centered_of_equal
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_nu_region

/-- The beta/rho bounds follow by averaging a copula and its survival copula. -/
theorem beta_rho_bounds (C : Copula 2) :
    C.spearmanRho ∈ Icc (betaLower C.blomqvistBeta) (betaUpper C.blomqvistBeta) := by
  have hu := beta_region_upper C
  have hus := beta_region_upper C.survivalCopula
  have hl := beta_region_lower C
  have hls := beta_region_lower C.survivalCopula
  rw [nu_survival, Copula.blomqvistBeta_survivalCopula] at hus hls
  constructor <;> linarith

theorem beta_upper_attained_joint (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧
      blestNu C = betaUpper b ∧ C.spearmanRho = betaUpper b := by
  let a : I := ⟨(1 - b) / 2, by constructor <;> linarith [hb.1, hb.2]⟩
  refine ⟨Verification.centeredOrdinal halfRotation a, ?_, ?_, ?_⟩
  · rw [Verification.centeredOrdinal_beta, halfRotation_values.2.2]
    dsimp [a]
    ring
  · rw [blest_centered_of_equal halfRotation
      (halfRotation_values.1.trans halfRotation_values.2.1.symm), halfRotation_values.2.1]
    dsimp [a, betaUpper]
    ring
  · rw [Verification.centeredOrdinal_rho, halfRotation_values.2.1]
    dsimp [a, betaUpper]
    ring

theorem beta_lower_attained_joint (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    ∃ C : Copula 2, C.blomqvistBeta = b ∧
      blestNu C = betaLower b ∧ C.spearmanRho = betaLower b := by
  obtain ⟨C, hc, hn, hr⟩ := beta_upper_attained_joint (-b) ⟨by linarith [hb.2], by linarith [hb.1]⟩
  refine ⟨C.reflect {1}, ?_, ?_, ?_⟩
  · rw [Copula.blomqvistBeta_reflect_second, hc]
    ring
  · rw [blest_reflect_second, hn]
    unfold betaUpper betaLower
    ring
  · rw [Copula.spearmanRho_reflect_second, hr]
    unfold betaUpper betaLower
    ring

theorem beta_rho_fibre (b r : ℝ) :
    (∃ C : Copula 2, C.blomqvistBeta = b ∧ C.spearmanRho = r) ↔
      b ∈ Icc (-1 : ℝ) 1 ∧ r ∈ Icc (betaLower b) (betaUpper b) := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    exact ⟨Copula.blomqvistBeta_mem_Icc C, beta_rho_bounds C⟩
  · rintro ⟨hb, hr⟩
    obtain ⟨Cu, hbu, _, hru⟩ := beta_upper_attained_joint b hb
    obtain ⟨Cl, hbl, _, hrl⟩ := beta_lower_attained_joint b hb
    have hc : Continuous (fun t : I => (Cu.mix Cl t).spearmanRho) := by
      simp_rw [Copula.spearmanRho_mix]
      fun_prop
    obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := r)
      (by simp only [Copula.spearmanRho_mix]; norm_num; rw [hrl]; exact hr.1)
      (by simp only [Copula.spearmanRho_mix]; norm_num; rw [hru]; exact hr.2)
    refine ⟨Cu.mix Cl t, ?_, ht⟩
    rw [Copula.blomqvistBeta_mix, hbu, hbl]
    ring

theorem beta_rho_region :
    Set.range (fun C : Copula 2 => (C.blomqvistBeta, C.spearmanRho)) =
      {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ∈ Icc (betaLower p.1) (betaUpper p.1)} := by
  ext ⟨b, r⟩
  simpa only [Set.mem_range, Set.mem_ofPred_eq, Prod.mk.injEq] using beta_rho_fibre b r

#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_rho_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_upper_attained_joint
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_lower_attained_joint
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_rho_fibre
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_rho_region

end
end Papers.Rockel2026ExactBlest
