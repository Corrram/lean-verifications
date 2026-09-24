import Papers.Rockel2026ExactBlest.ExactBlest

/-! The unconditional Blest--beta inequality in exact-blest-regions.tex.
The certificate below is checked as an exact polynomial identity in each rectangle.
No numeric solver or assumed beta-region theorem enters the proof. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section

set_option maxHeartbeats 1600000

def betaPhi0 (x : ℝ) : ℝ := 2 * x ^ 3 / 3
def betaPhi1 (x : ℝ) : ℝ := 2 * x ^ 3 / 3 + x ^ 2 / 3 - 1 / 108
def betaPhi2 (x : ℝ) : ℝ := 2 * x ^ 3 / 3 - x ^ 2 / 3 + 13 / 324
def betaPhi3 (x : ℝ) : ℝ := 2 * x ^ 3 / 3 - 31 / 162
def betaPsi0 (z : ℝ) : ℝ := z ^ 3 / 3
def betaPsi1 (z : ℝ) : ℝ := z ^ 3 / 3 + z ^ 2 / 3 + z / 9 - 1 / 36
def betaPsi2 (z : ℝ) : ℝ := z ^ 3 / 3 - z ^ 2 / 3 + z / 9 - 1 / 324
def betaPsi3 (z : ℝ) : ℝ := z ^ 3 / 3 - 23 / 162

def bernsteinRow (a b c d t : ℝ) : ℝ :=
  a * (1 - t) ^ 3 + 3 * b * t * (1 - t) ^ 2 + 3 * c * t ^ 2 * (1 - t) + d * t ^ 3

theorem bernsteinRow_nonneg (a b c d t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    0 ≤ bernsteinRow a b c d t := by
  have ht0 := ht.1
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2]
  unfold bernsteinRow
  positivity

theorem beta_cell_00 (x z : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 6))
    (hz : z ∈ Icc (0 : ℝ) (1 / 6)) :
    0 ≤ betaPhi0 x + betaPsi0 z - x ^ 2 * z := by
  have he : betaPhi0 x + betaPsi0 z - x ^ 2 * z = (x - z) ^ 2 * (2 * x + z) / 3 := by
    unfold betaPhi0 betaPsi0
    ring
  rw [he]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hz0 : 0 ≤ z := by linarith [hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_00

theorem beta_cell_01 (x z : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 6))
    (hz : z ∈ Icc ((1 / 6) : ℝ) (1 / 2)) :
    0 ≤ betaPhi0 x + betaPsi1 z - x ^ 2 * z := by
  have hu : ((x - 0) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (1 / 6)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi0 x + betaPsi1 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (1 / 648) (19 / 648) (49 / 648) (11 / 72) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow (1 / 648) (19 / 648) (49 / 648) (11 / 72) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow 0 (13 / 486) (35 / 486) (4 / 27) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow 0 (2 / 81) (11 / 162) (23 / 162) ((z - (1 / 6)) / (1 / 3)))
      ((x - 0) / (1 / 6)) := by
    unfold betaPhi0 betaPsi1 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_01

theorem beta_cell_02 (x z : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 6))
    (hz : z ∈ Icc ((1 / 2) : ℝ) (5 / 6)) :
    0 ≤ betaPhi0 x + betaPsi2 z - x ^ 2 * z := by
  have hu : ((x - 0) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (1 / 2)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi0 x + betaPsi2 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (7 / 648) (1 / 72) (5 / 216) (11 / 216) ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (7 / 648) (1 / 72) (5 / 216) (11 / 216) ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (1 / 162) (2 / 243) (4 / 243) (7 / 162) ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow 0 0 (1 / 162) (5 / 162) ((z - (1 / 2)) / (1 / 3)))
      ((x - 0) / (1 / 6)) := by
    unfold betaPhi0 betaPsi2 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_02

theorem beta_cell_03 (x z : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 6))
    (hz : z ∈ Icc ((5 / 6) : ℝ) 1) :
    0 ≤ betaPhi0 x + betaPsi3 z - x ^ 2 * z := by
  have hu : ((x - 0) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (5 / 6)) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi0 x + betaPsi3 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (11 / 216) (29 / 324) (11 / 81) (31 / 162) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow (11 / 216) (29 / 324) (11 / 81) (31 / 162) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow (7 / 162) (79 / 972) (247 / 1944) (59 / 324) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow (5 / 162) (11 / 162) (73 / 648) (1 / 6) ((z - (5 / 6)) / (1 / 6)))
      ((x - 0) / (1 / 6)) := by
    unfold betaPhi0 betaPsi3 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_03

theorem beta_cell_10 (x z : ℝ) (hx : x ∈ Icc ((1 / 6) : ℝ) (1 / 2))
    (hz : z ∈ Icc (0 : ℝ) (1 / 6)) :
    0 ≤ betaPhi1 x + betaPsi0 z - x ^ 2 * z := by
  have hu : ((x - (1 / 6)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - 0) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi1 x + betaPsi0 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (1 / 324) (1 / 648) 0 0 ((z - 0) / (1 / 6)))
      (bernsteinRow (7 / 324) (35 / 1944) (7 / 486) (1 / 81) ((z - 0) / (1 / 6)))
      (bernsteinRow (7 / 108) (37 / 648) (4 / 81) (7 / 162) ((z - 0) / (1 / 6)))
      (bernsteinRow (17 / 108) (31 / 216) (7 / 54) (19 / 162) ((z - 0) / (1 / 6)))
      ((x - (1 / 6)) / (1 / 3)) := by
    unfold betaPhi1 betaPsi0 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_10

theorem beta_cell_11 (x z : ℝ) (hx : x ∈ Icc ((1 / 6) : ℝ) (1 / 2))
    (hz : z ∈ Icc ((1 / 6) : ℝ) (1 / 2)) :
    0 ≤ betaPhi1 x + betaPsi1 z - x ^ 2 * z := by
  have hu : ((x - (1 / 6)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (1 / 6)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi1 x + betaPsi1 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow 0 (2 / 81) (11 / 162) (23 / 162) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow (1 / 81) (8 / 243) (35 / 486) (23 / 162) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow (7 / 162) (1 / 18) (7 / 81) (4 / 27) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow (19 / 162) (19 / 162) (11 / 81) (5 / 27) ((z - (1 / 6)) / (1 / 3)))
      ((x - (1 / 6)) / (1 / 3)) := by
    unfold betaPhi1 betaPsi1 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_11

theorem beta_cell_12 (x z : ℝ) (hx : x ∈ Icc ((1 / 6) : ℝ) (1 / 2))
    (hz : z ∈ Icc ((1 / 2) : ℝ) (5 / 6)) :
    0 ≤ betaPhi1 x + betaPsi2 z - x ^ 2 * z := by
  have he : betaPhi1 x + betaPsi2 z - x ^ 2 * z = (3 * x - 3 * z + 1) ^ 2 * (6 * x + 3 * z - 1) / 81 := by
    unfold betaPhi1 betaPsi2
    ring
  rw [he]
  have hp : 0 ≤ 6 * x + 3 * z - 1 := by linarith [hx.1, hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_12

theorem beta_cell_13 (x z : ℝ) (hx : x ∈ Icc ((1 / 6) : ℝ) (1 / 2))
    (hz : z ∈ Icc ((5 / 6) : ℝ) 1) :
    0 ≤ betaPhi1 x + betaPsi3 z - x ^ 2 * z := by
  have hu : ((x - (1 / 6)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (5 / 6)) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi1 x + betaPsi3 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (5 / 162) (11 / 162) (73 / 648) (1 / 6) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow (1 / 54) (13 / 243) (187 / 1944) (4 / 27) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow 0 (5 / 162) (5 / 72) (19 / 162) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow 0 (2 / 81) (37 / 648) (8 / 81) ((z - (5 / 6)) / (1 / 6)))
      ((x - (1 / 6)) / (1 / 3)) := by
    unfold betaPhi1 betaPsi3 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_13

theorem beta_cell_20 (x z : ℝ) (hx : x ∈ Icc ((1 / 2) : ℝ) (5 / 6))
    (hz : z ∈ Icc (0 : ℝ) (1 / 6)) :
    0 ≤ betaPhi2 x + betaPsi0 z - x ^ 2 * z := by
  have hu : ((x - (1 / 2)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - 0) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi2 x + betaPsi0 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (13 / 324) (17 / 648) (1 / 81) 0 ((z - 0) / (1 / 6)))
      (bernsteinRow (19 / 324) (25 / 648) (1 / 54) 0 ((z - 0) / (1 / 6)))
      (bernsteinRow (11 / 108) (143 / 1944) (11 / 243) (1 / 54) ((z - 0) / (1 / 6)))
      (bernsteinRow (7 / 36) (101 / 648) (19 / 162) (13 / 162) ((z - 0) / (1 / 6)))
      ((x - (1 / 2)) / (1 / 3)) := by
    unfold betaPhi2 betaPsi0 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_20

theorem beta_cell_21 (x z : ℝ) (hx : x ∈ Icc ((1 / 2) : ℝ) (5 / 6))
    (hz : z ∈ Icc ((1 / 6) : ℝ) (1 / 2)) :
    0 ≤ betaPhi2 x + betaPsi1 z - x ^ 2 * z := by
  have he : betaPhi2 x + betaPsi1 z - x ^ 2 * z = (3 * x - 3 * z - 1) ^ 2 * (6 * x + 3 * z + 1) / 81 := by
    unfold betaPhi2 betaPsi1
    ring
  rw [he]
  have hp : 0 ≤ 6 * x + 3 * z + 1 := by linarith [hx.1, hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_21

theorem beta_cell_22 (x z : ℝ) (hx : x ∈ Icc ((1 / 2) : ℝ) (5 / 6))
    (hz : z ∈ Icc ((1 / 2) : ℝ) (5 / 6)) :
    0 ≤ betaPhi2 x + betaPsi2 z - x ^ 2 * z + 1 / 3 := by
  have hu : ((x - (1 / 2)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (1 / 2)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi2 x + betaPsi2 z - x ^ 2 * z + 1 / 3 = bernsteinRow
      (bernsteinRow (7 / 27) (19 / 81) (35 / 162) (35 / 162) ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (2 / 9) (5 / 27) (25 / 162) (23 / 162) ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (31 / 162) (67 / 486) (22 / 243) (5 / 81) ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (31 / 162) (19 / 162) (4 / 81) 0 ((z - (1 / 2)) / (1 / 3)))
      ((x - (1 / 2)) / (1 / 3)) := by
    unfold betaPhi2 betaPsi2 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_22

theorem beta_cell_23 (x z : ℝ) (hx : x ∈ Icc ((1 / 2) : ℝ) (5 / 6))
    (hz : z ∈ Icc ((5 / 6) : ℝ) 1) :
    0 ≤ betaPhi2 x + betaPsi3 z - x ^ 2 * z + 1 / 3 := by
  have hu : ((x - (1 / 2)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (5 / 6)) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi2 x + betaPsi3 z - x ^ 2 * z + 1 / 3 = bernsteinRow
      (bernsteinRow (35 / 162) (13 / 54) (59 / 216) (17 / 54) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow (23 / 162) (13 / 81) (121 / 648) (2 / 9) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow (5 / 81) (35 / 486) (175 / 1944) (19 / 162) ((z - (5 / 6)) / (1 / 6)))
      (bernsteinRow 0 0 (5 / 648) (2 / 81) ((z - (5 / 6)) / (1 / 6)))
      ((x - (1 / 2)) / (1 / 3)) := by
    unfold betaPhi2 betaPsi3 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_23

theorem beta_cell_30 (x z : ℝ) (hx : x ∈ Icc ((5 / 6) : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) (1 / 6)) :
    0 ≤ betaPhi3 x + betaPsi0 z - x ^ 2 * z := by
  have hu : ((x - (5 / 6)) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - 0) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi3 x + betaPsi0 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (7 / 36) (101 / 648) (19 / 162) (13 / 162) ((z - 0) / (1 / 6)))
      (bernsteinRow (22 / 81) (443 / 1944) (179 / 972) (23 / 162) ((z - 0) / (1 / 6)))
      (bernsteinRow (59 / 162) (17 / 54) (43 / 162) (47 / 216) ((z - 0) / (1 / 6)))
      (bernsteinRow (77 / 162) (34 / 81) (59 / 162) (67 / 216) ((z - 0) / (1 / 6)))
      ((x - (5 / 6)) / (1 / 6)) := by
    unfold betaPhi3 betaPsi0 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_30

theorem beta_cell_31 (x z : ℝ) (hx : x ∈ Icc ((5 / 6) : ℝ) 1)
    (hz : z ∈ Icc ((1 / 6) : ℝ) (1 / 2)) :
    0 ≤ betaPhi3 x + betaPsi1 z - x ^ 2 * z := by
  have hu : ((x - (5 / 6)) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (1 / 6)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi3 x + betaPsi1 z - x ^ 2 * z = bernsteinRow
      (bernsteinRow (13 / 162) (5 / 162) 0 0 ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow (23 / 162) (20 / 243) (10 / 243) (5 / 162) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow (47 / 216) (95 / 648) (61 / 648) (47 / 648) ((z - (1 / 6)) / (1 / 3)))
      (bernsteinRow (67 / 216) (49 / 216) (35 / 216) (83 / 648) ((z - (1 / 6)) / (1 / 3)))
      ((x - (5 / 6)) / (1 / 6)) := by
    unfold betaPhi3 betaPsi1 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_31

theorem beta_cell_32 (x z : ℝ) (hx : x ∈ Icc ((5 / 6) : ℝ) 1)
    (hz : z ∈ Icc ((1 / 2) : ℝ) (5 / 6)) :
    0 ≤ betaPhi3 x + betaPsi2 z - x ^ 2 * z + 1 / 3 := by
  have hu : ((x - (5 / 6)) / (1 / 6)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
  have hv : ((z - (1 / 2)) / (1 / 3)) ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hz.1, hz.2]
  have he : betaPhi3 x + betaPsi2 z - x ^ 2 * z + 1 / 3 = bernsteinRow
      (bernsteinRow (31 / 162) (19 / 162) (4 / 81) 0 ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (2 / 9) (67 / 486) (29 / 486) 0 ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (19 / 72) (109 / 648) (17 / 216) (5 / 648) ((z - (1 / 2)) / (1 / 3)))
      (bernsteinRow (23 / 72) (137 / 648) (71 / 648) (17 / 648) ((z - (1 / 2)) / (1 / 3)))
      ((x - (5 / 6)) / (1 / 6)) := by
    unfold betaPhi3 betaPsi2 bernsteinRow
    ring
  rw [he]
  apply bernsteinRow_nonneg _ _ _ _ _ hu <;>
    (apply bernsteinRow_nonneg _ _ _ _ _ hv <;> norm_num)
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_32

theorem beta_cell_33 (x z : ℝ) (hx : x ∈ Icc ((5 / 6) : ℝ) 1)
    (hz : z ∈ Icc ((5 / 6) : ℝ) 1) :
    0 ≤ betaPhi3 x + betaPsi3 z - x ^ 2 * z + 1 / 3 := by
  have he : betaPhi3 x + betaPsi3 z - x ^ 2 * z + 1 / 3 = (x - z) ^ 2 * (2 * x + z) / 3 := by
    unfold betaPhi3 betaPsi3
    ring
  rw [he]
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hz0 : 0 ≤ z := by linarith [hz.1]
  positivity
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_cell_33

#assert_standard_axioms Papers.Rockel2026ExactBlest.bernsteinRow_nonneg

def fourPiece (f0 f1 f2 f3 : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ≤ 1 / 6 then f0 x else if x ≤ 1 / 2 then f1 x else if x ≤ 5 / 6 then f2 x else f3 x
def betaPhi : ℝ → ℝ := fourPiece betaPhi0 betaPhi1 betaPhi2 betaPhi3
def betaPsi : ℝ → ℝ := fourPiece betaPsi0 betaPsi1 betaPsi2 betaPsi3
def cutValue (f : ℝ → ℝ) (t x : ℝ) : ℝ := if x ≤ t then f x else 0

theorem integral_cutValue (f : ℝ → ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ u : I, cutValue f t u) = ∫ x in (0 : ℝ)..t, f x := by
  classical
  change (∫ u : I, (Set.indicator {x : ℝ | x ≤ t} f) u) = _
  rw [Copula.integral_unitInterval (Set.indicator {x : ℝ | x ≤ t} f),
    intervalIntegral.integral_indicator ht]

theorem integrable_cutValue (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    Integrable (fun u : I => cutValue f t u) := by
  classical
  exact (Copula.integrable_continuous_unit _ (show Continuous (fun u : I => f u) by
    fun_prop)).indicator (measurableSet_le measurable_subtype_coe measurable_const)

theorem fourPiece_decomposition (f0 f1 f2 f3 : ℝ → ℝ) :
    fourPiece f0 f1 f2 f3 = fun x => f3 x + cutValue (fun x => f2 x - f3 x) (5 / 6) x +
      cutValue (fun x => f1 x - f2 x) (1 / 2) x + cutValue (fun x => f0 x - f1 x) (1 / 6) x := by
  funext x
  unfold fourPiece cutValue
  split_ifs <;> linarith

theorem integral_fourPiece (f0 f1 f2 f3 : ℝ → ℝ)
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) :
    (∫ u : I, fourPiece f0 f1 f2 f3 u) = (∫ u : I, f3 u) +
      (∫ x in (0 : ℝ)..(5 / 6), f2 x - f3 x) +
      (∫ x in (0 : ℝ)..(1 / 2), f1 x - f2 x) +
      (∫ x in (0 : ℝ)..(1 / 6), f0 x - f1 x) := by
  have hi3 : Integrable (fun u : I => f3 u) := Copula.integrable_continuous_unit _ (by fun_prop)
  have hi2 := integrable_cutValue (fun x => f2 x - f3 x) (h2.sub h3) (5 / 6)
  have hi1 := integrable_cutValue (fun x => f1 x - f2 x) (h1.sub h2) (1 / 2)
  have hi0 := integrable_cutValue (fun x => f0 x - f1 x) (h0.sub h1) (1 / 6)
  rw [fourPiece_decomposition]
  dsimp only
  have ha0 := integral_add ((hi3.add hi2).add hi1) hi0
  have ha1 := integral_add (hi3.add hi2) hi1
  have ha2 := integral_add hi3 hi2
  simp only [Pi.add_apply] at ha0 ha1 ha2
  rw [ha0, ha1, ha2,
    integral_cutValue _ _ (by norm_num), integral_cutValue _ _ (by norm_num),
    integral_cutValue _ _ (by norm_num)]

theorem integrable_fourPiece (C : Copula 2) (i : Fin 2) (f0 f1 f2 f3 : ℝ → ℝ)
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) :
    Integrable (fun x => fourPiece f0 f1 f2 f3 (x i)) C.toMeasure := by
  classical
  have hf (f : ℝ → ℝ) (hf : Continuous f) : Integrable (fun x : Fin 2 → I => f (x i)) C.toMeasure :=
    Copula.integrable_continuous_cube _ (by fun_prop)
  have hm (t : ℝ) : MeasurableSet {x : Fin 2 → I | (x i : ℝ) ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  exact Integrable.piecewise (hm _) (hf f0 h0).integrableOn
    (Integrable.piecewise (hm _) (hf f1 h1).integrableOn
      (Integrable.piecewise (hm _) (hf f2 h2).integrableOn (hf f3 h3).integrableOn).integrableOn).integrableOn

theorem measurable_fourPiece (f0 f1 f2 f3 : ℝ → ℝ)
    (h0 : Continuous f0) (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3) :
    Measurable (fun u : I => fourPiece f0 f1 f2 f3 u) := by
  have hf (f : ℝ → ℝ) (hf : Continuous f) : Measurable (fun u : I => f u) := by fun_prop
  have hm (t : ℝ) : MeasurableSet {u : I | (u : ℝ) ≤ t} :=
    measurableSet_le measurable_subtype_coe measurable_const
  exact (hf f0 h0).ite (hm _) ((hf f1 h1).ite (hm _) ((hf f2 h2).ite (hm _) (hf f3 h3)))

theorem beta_dual (x z : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1) :
    x ^ 2 * z - (if 1 / 2 < x ∧ 1 / 2 < z then (1 : ℝ) else 0) / 3 ≤ betaPhi x + betaPsi z := by
  by_cases hx0 : x ≤ (1 / 6)
  ·
    by_cases hz0 : z ≤ (1 / 6)
    ·
      have hc := beta_cell_00 x z
        (by constructor <;> linarith [hx.1, hx.2])
        (by constructor <;> linarith [hz.1, hz.2])
      have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
        rintro ⟨hqx, hqz⟩
        linarith
      simp only [betaPhi, betaPsi, fourPiece, ite_eq_left hx0, ite_eq_left hz0, ite_eq_right hq]
      linarith
    ·
      by_cases hz1 : z ≤ (1 / 2)
      ·
        have hc := beta_cell_01 x z
          (by constructor <;> linarith [hx.1, hx.2])
          (by constructor <;> linarith [hz.1, hz.2])
        have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
          rintro ⟨hqx, hqz⟩
          linarith
        simp only [betaPhi, betaPsi, fourPiece, ite_eq_left hx0, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hq]
        linarith
      ·
        by_cases hz2 : z ≤ (5 / 6)
        ·
          have hc := beta_cell_02 x z
            (by constructor <;> linarith [hx.1, hx.2])
            (by constructor <;> linarith [hz.1, hz.2])
          have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith
          simp only [betaPhi, betaPsi, fourPiece, ite_eq_left hx0, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_right hq]
          linarith
        ·
          have hc := beta_cell_03 x z
            (by constructor <;> linarith [hx.1, hx.2])
            (by constructor <;> linarith [hz.1, hz.2])
          have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith
          simp only [betaPhi, betaPsi, fourPiece, ite_eq_left hx0, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_right hq]
          linarith
  ·
    by_cases hx1 : x ≤ (1 / 2)
    ·
      by_cases hz0 : z ≤ (1 / 6)
      ·
        have hc := beta_cell_10 x z
          (by constructor <;> linarith [hx.1, hx.2])
          (by constructor <;> linarith [hz.1, hz.2])
        have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
          rintro ⟨hqx, hqz⟩
          linarith
        simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_left hx1, ite_eq_left hz0, ite_eq_right hq]
        linarith
      ·
        by_cases hz1 : z ≤ (1 / 2)
        ·
          have hc := beta_cell_11 x z
            (by constructor <;> linarith [hx.1, hx.2])
            (by constructor <;> linarith [hz.1, hz.2])
          have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith
          simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_left hx1, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hq]
          linarith
        ·
          by_cases hz2 : z ≤ (5 / 6)
          ·
            have hc := beta_cell_12 x z
              (by constructor <;> linarith [hx.1, hx.2])
              (by constructor <;> linarith [hz.1, hz.2])
            have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith
            simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_left hx1, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_right hq]
            linarith
          ·
            have hc := beta_cell_13 x z
              (by constructor <;> linarith [hx.1, hx.2])
              (by constructor <;> linarith [hz.1, hz.2])
            have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith
            simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_left hx1, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_right hq]
            linarith
    ·
      by_cases hx2 : x ≤ (5 / 6)
      ·
        by_cases hz0 : z ≤ (1 / 6)
        ·
          have hc := beta_cell_20 x z
            (by constructor <;> linarith [hx.1, hx.2])
            (by constructor <;> linarith [hz.1, hz.2])
          have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith
          simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_left hz0, ite_eq_right hq]
          linarith
        ·
          by_cases hz1 : z ≤ (1 / 2)
          ·
            have hc := beta_cell_21 x z
              (by constructor <;> linarith [hx.1, hx.2])
              (by constructor <;> linarith [hz.1, hz.2])
            have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith
            simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hq]
            linarith
          ·
            by_cases hz2 : z ≤ (5 / 6)
            ·
              have hc := beta_cell_22 x z
                (by constructor <;> linarith [hx.1, hx.2])
                (by constructor <;> linarith [hz.1, hz.2])
              have hq : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith
              simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_left hq]
              linarith
            ·
              have hc := beta_cell_23 x z
                (by constructor <;> linarith [hx.1, hx.2])
                (by constructor <;> linarith [hz.1, hz.2])
              have hq : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith
              simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_left hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_left hq]
              linarith
      ·
        by_cases hz0 : z ≤ (1 / 6)
        ·
          have hc := beta_cell_30 x z
            (by constructor <;> linarith [hx.1, hx.2])
            (by constructor <;> linarith [hz.1, hz.2])
          have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
            rintro ⟨hqx, hqz⟩
            linarith
          simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_left hz0, ite_eq_right hq]
          linarith
        ·
          by_cases hz1 : z ≤ (1 / 2)
          ·
            have hc := beta_cell_31 x z
              (by constructor <;> linarith [hx.1, hx.2])
              (by constructor <;> linarith [hz.1, hz.2])
            have hq : ¬(1 / 2 < x ∧ 1 / 2 < z) := by
              rintro ⟨hqx, hqz⟩
              linarith
            simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hz0, ite_eq_left hz1, ite_eq_right hq]
            linarith
          ·
            by_cases hz2 : z ≤ (5 / 6)
            ·
              have hc := beta_cell_32 x z
                (by constructor <;> linarith [hx.1, hx.2])
                (by constructor <;> linarith [hz.1, hz.2])
              have hq : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith
              simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_left hz2, ite_eq_left hq]
              linarith
            ·
              have hc := beta_cell_33 x z
                (by constructor <;> linarith [hx.1, hx.2])
                (by constructor <;> linarith [hz.1, hz.2])
              have hq : 1 / 2 < x ∧ 1 / 2 < z := by constructor <;> linarith
              simp only [betaPhi, betaPsi, fourPiece, ite_eq_right hx0, ite_eq_right hx1, ite_eq_right hx2, ite_eq_right hz0, ite_eq_right hz1, ite_eq_right hz2, ite_eq_left hq]
              linarith

#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_dual

theorem integral_betaPhi : (∫ u : I, betaPhi u) = (35 / 324) := by
  rw [betaPhi, integral_fourPiece _ _ _ _
    (by unfold betaPhi0; fun_prop) (by unfold betaPhi1; fun_prop)
    (by unfold betaPhi2; fun_prop) (by unfold betaPhi3; fun_prop)]
  have he0 : betaPhi3 = fun x : ℝ => (2 / 3) * x ^ 3 + 0 * x ^ 2 + 0 * x + (-31 / 162) := by
    funext x; unfold betaPhi3; ring
  have he1 : (fun x : ℝ => betaPhi2 x - betaPhi3 x) = fun x : ℝ => 0 * x ^ 3 + (-1 / 3) * x ^ 2 + 0 * x + (25 / 108) := by
    funext x; unfold betaPhi2 betaPhi3; ring
  have he2 : (fun x : ℝ => betaPhi1 x - betaPhi2 x) = fun x : ℝ => 0 * x ^ 3 + (2 / 3) * x ^ 2 + 0 * x + (-4 / 81) := by
    funext x; unfold betaPhi1 betaPhi2; ring
  have he3 : (fun x : ℝ => betaPhi0 x - betaPhi1 x) = fun x : ℝ => 0 * x ^ 3 + (-1 / 3) * x ^ 2 + 0 * x + (1 / 108) := by
    funext x; unfold betaPhi0 betaPhi1; ring
  rw [he1, he2, he3, he0, Copula.integral_unitInterval (fun x : ℝ => (2 / 3) * x ^ 3 + 0 * x ^ 2 + 0 * x + (-31 / 162)),
    integral_poly3, integral_poly3, integral_poly3, integral_poly3]
  norm_num
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_betaPhi

theorem integral_betaPsi : (∫ u : I, betaPsi u) = (4 / 81) := by
  rw [betaPsi, integral_fourPiece _ _ _ _
    (by unfold betaPsi0; fun_prop) (by unfold betaPsi1; fun_prop)
    (by unfold betaPsi2; fun_prop) (by unfold betaPsi3; fun_prop)]
  have he0 : betaPsi3 = fun x : ℝ => (1 / 3) * x ^ 3 + 0 * x ^ 2 + 0 * x + (-23 / 162) := by
    funext x; unfold betaPsi3; ring
  have he1 : (fun x : ℝ => betaPsi2 x - betaPsi3 x) = fun x : ℝ => 0 * x ^ 3 + (-1 / 3) * x ^ 2 + (1 / 9) * x + (5 / 36) := by
    funext x; unfold betaPsi2 betaPsi3; ring
  have he2 : (fun x : ℝ => betaPsi1 x - betaPsi2 x) = fun x : ℝ => 0 * x ^ 3 + (2 / 3) * x ^ 2 + 0 * x + (-2 / 81) := by
    funext x; unfold betaPsi1 betaPsi2; ring
  have he3 : (fun x : ℝ => betaPsi0 x - betaPsi1 x) = fun x : ℝ => 0 * x ^ 3 + (-1 / 3) * x ^ 2 + (-1 / 9) * x + (1 / 36) := by
    funext x; unfold betaPsi0 betaPsi1; ring
  rw [he1, he2, he3, he0, Copula.integral_unitInterval (fun x : ℝ => (1 / 3) * x ^ 3 + 0 * x ^ 2 + 0 * x + (-23 / 162)),
    integral_poly3, integral_poly3, integral_poly3, integral_poly3]
  norm_num
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_betaPsi
def upperQuadrant (x : Fin 2 → I) : ℝ :=
  if (1 / 2 : ℝ) < x 0 ∧ (1 / 2 : ℝ) < x 1 then 1 else 0

theorem integrable_upperQuadrant (C : Copula 2) : Integrable upperQuadrant C.toMeasure := by
  classical
  have hm : MeasurableSet {x : Fin 2 → I | (1 / 2 : ℝ) < x 0 ∧ (1 / 2 : ℝ) < x 1} :=
    (measurableSet_lt (show Measurable (fun _ : Fin 2 → I => (1 / 2 : ℝ)) from measurable_const)
      (show Measurable (fun x : Fin 2 → I => (x 0 : ℝ)) by fun_prop)).inter
      (measurableSet_lt (show Measurable (fun _ : Fin 2 → I => (1 / 2 : ℝ)) from measurable_const)
        (show Measurable (fun x : Fin 2 → I => (x 1 : ℝ)) by fun_prop))
  refine ((integrable_const (μ := C.toMeasure) (1 : ℝ)).indicator hm).congr
    (Filter.Eventually.of_forall fun x => ?_)
  simp [upperQuadrant, Set.indicator]

theorem integral_upperQuadrant (C : Copula 2) :
    (∫ x, upperQuadrant x ∂C.toMeasure) = C.cdf ![Copula.unitHalf, Copula.unitHalf] := by
  classical
  have hi (i : Fin 2) : Integrable (fun x : Fin 2 → I => if (x i : ℝ) ≤ 1 / 2 then (1 : ℝ) else 0)
      C.toMeasure :=
    (integrable_const (1 : ℝ)).indicator
      (measurableSet_le (show Measurable (fun x : Fin 2 → I => (x i : ℝ)) by fun_prop) measurable_const)
  have hb : Integrable (fun x => if x ≤ ![Copula.unitHalf, Copula.unitHalf] then (1 : ℝ) else 0)
      C.toMeasure := by
    refine ((integrable_const (μ := C.toMeasure) (1 : ℝ)).indicator
      (show MeasurableSet (Iic ![Copula.unitHalf, Copula.unitHalf]) from measurableSet_Iic)).congr
        (Filter.Eventually.of_forall fun x => ?_)
    simp [Set.indicator]
  have hu : (∫ u : I, if (u : ℝ) ≤ 1 / 2 then (1 : ℝ) else 0) = 1 / 2 := by
    have h := integral_indicator_one (μ := (volume : Measure I)) (s := Iic Copula.unitHalf) measurableSet_Iic
    have he : (fun u : I => if u ≤ Copula.unitHalf then (1 : ℝ) else 0) =
        fun u : I => if (u : ℝ) ≤ 1 / 2 then (1 : ℝ) else 0 := by
      funext u
      simp only [show u ≤ Copula.unitHalf ↔ (u : ℝ) ≤ 1 / 2 from Iff.rfl]
    simp only [Set.indicator, Set.mem_Iic, Pi.one_apply] at h
    rw [he] at h
    simpa [Measure.real, unitInterval.volume_Iic, Copula.unitHalf] using h
  have hm (i : Fin 2) : (∫ x, if (x i : ℝ) ≤ 1 / 2 then (1 : ℝ) else 0 ∂C.toMeasure) = 1 / 2 := by
    rw [C.integral_eval i (fun u : I => if (u : ℝ) ≤ 1 / 2 then (1 : ℝ) else 0)
      (measurable_const.ite (measurableSet_le measurable_subtype_coe measurable_const) measurable_const), hu]
  have hc : (∫ x, if x ≤ ![Copula.unitHalf, Copula.unitHalf] then (1 : ℝ) else 0 ∂C.toMeasure) =
      C.cdf ![Copula.unitHalf, Copula.unitHalf] := by
    simpa [Set.indicator, Copula.cdf] using
      integral_indicator_one (μ := C.toMeasure) (s := Iic ![Copula.unitHalf, Copula.unitHalf]) measurableSet_Iic
  have he : upperQuadrant = fun x : Fin 2 → I =>
      1 - (if (x 0 : ℝ) ≤ 1 / 2 then (1 : ℝ) else 0) -
        (if (x 1 : ℝ) ≤ 1 / 2 then (1 : ℝ) else 0) +
        (if x ≤ ![Copula.unitHalf, Copula.unitHalf] then (1 : ℝ) else 0) := by
    funext x
    have hp : x ≤ ![Copula.unitHalf, Copula.unitHalf] ↔
        (x 0 : ℝ) ≤ 1 / 2 ∧ (x 1 : ℝ) ≤ 1 / 2 := by
      simp only [Pi.le_def, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rfl
    simp only [hp]
    unfold upperQuadrant
    by_cases h0 : (x 0 : ℝ) ≤ 1 / 2 <;> by_cases h1 : (x 1 : ℝ) ≤ 1 / 2 <;>
      simp only [lt_iff_not_ge, h0, h1] <;> norm_num
  have ha := integral_add (((integrable_const (1 : ℝ)).sub (hi 0)).sub (hi 1)) hb
  have hs1 := integral_sub ((integrable_const (1 : ℝ)).sub (hi 0)) (hi 1)
  have hs0 := integral_sub (integrable_const (1 : ℝ)) (hi 0)
  simp only [Pi.sub_apply] at ha hs1 hs0
  rw [he]
  dsimp only
  rw [ha, hs1, hs0, hm, hm, hc]
  norm_num

theorem beta_quadrant_formula (C : Copula 2) :
    C.blomqvistBeta = 4 * (∫ x, upperQuadrant x ∂C.toMeasure) - 1 := by
  rw [integral_upperQuadrant]
  rfl

theorem transport_beta_upper (C : Copula 2) :
    (∫ x, (x 0 : ℝ) ^ 2 * (x 1 : ℝ) - upperQuadrant x / 3 ∂C.toMeasure) ≤ 17 / 108 := by
  have hp : Integrable (fun x : Fin 2 → I => betaPhi (x 0)) C.toMeasure :=
    integrable_fourPiece C 0 _ _ _ _ (by unfold betaPhi0; fun_prop)
      (by unfold betaPhi1; fun_prop) (by unfold betaPhi2; fun_prop) (by unfold betaPhi3; fun_prop)
  have hq : Integrable (fun x : Fin 2 → I => betaPsi (x 1)) C.toMeasure :=
    integrable_fourPiece C 1 _ _ _ _ (by unfold betaPsi0; fun_prop)
      (by unfold betaPsi1; fun_prop) (by unfold betaPsi2; fun_prop) (by unfold betaPsi3; fun_prop)
  have hi : Integrable (fun x : Fin 2 → I => (x 0 : ℝ) ^ 2 * (x 1 : ℝ) - upperQuadrant x / 3)
      C.toMeasure :=
    (Copula.integrable_continuous_cube _ (by fun_prop)).sub ((integrable_upperQuadrant C).div_const 3)
  have h := integral_mono hi (hp.add hq) (fun x => beta_dual (x 0) (x 1) (x 0).property (x 1).property)
  simp only [Pi.add_apply] at h
  rw [integral_add hp hq,
    C.integral_eval 0 (fun u : I => betaPhi u) (measurable_fourPiece _ _ _ _
      (by unfold betaPhi0; fun_prop) (by unfold betaPhi1; fun_prop)
      (by unfold betaPhi2; fun_prop) (by unfold betaPhi3; fun_prop)),
    C.integral_eval 1 (fun u : I => betaPsi u) (measurable_fourPiece _ _ _ _
      (by unfold betaPsi0; fun_prop) (by unfold betaPsi1; fun_prop)
      (by unfold betaPsi2; fun_prop) (by unfold betaPsi3; fun_prop)),
    integral_betaPhi, integral_betaPsi] at h
  linarith

theorem nu_beta_upper (C : Copula 2) : blestNu C - C.blomqvistBeta ≤ 8 / 9 := by
  have hn := support_moment_survival C 0
  norm_num [cost] at hn
  have hb := beta_quadrant_formula C.survivalCopula
  rw [Copula.blomqvistBeta_survivalCopula] at hb
  have h := transport_beta_upper C.survivalCopula
  rw [integral_sub (Copula.integrable_continuous_cube _ (by fun_prop))
    ((integrable_upperQuadrant _).div_const 3), integral_div] at h
  linarith

/-- The manuscript's unconditional bound; no exact-region hypothesis is assumed. -/
theorem nu_beta_bound (C : Copula 2) : |blestNu C - C.blomqvistBeta| ≤ 8 / 9 := by
  have hu := nu_beta_upper C
  have hl := nu_beta_upper (C.reflect {1})
  rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second] at hl
  exact abs_le.mpr ⟨by linarith, hu⟩

#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_cutValue
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_cutValue
#assert_standard_axioms Papers.Rockel2026ExactBlest.fourPiece_decomposition
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_fourPiece
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_fourPiece
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_fourPiece
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_upperQuadrant
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_upperQuadrant
#assert_standard_axioms Papers.Rockel2026ExactBlest.beta_quadrant_formula
#assert_standard_axioms Papers.Rockel2026ExactBlest.transport_beta_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_upper
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_bound

theorem raw_blest_moment (C : Copula 2) :
    12 * (∫ x, (x 0 : ℝ) ^ 2 * (x 1 : ℝ) ∂C.toMeasure) - 2 = 2 * C.spearmanRho - blestNu C := by
  have h := support_moment_survival C.survivalCopula 0
  rw [Copula.survivalCopula_survivalCopula, nu_survival] at h
  norm_num [cost] at h
  linarith

theorem blest_ordinalSum (C D : Copula 2) (a : I) :
    blestNu (C.ordinalSum D a) = (a : ℝ) ^ 4 * blestNu C + (1 - (a : ℝ)) ^ 4 * blestNu D +
      2 * (a : ℝ) ^ 3 * (1 - (a : ℝ)) * C.spearmanRho + 2 * (a : ℝ) * (1 - (a : ℝ)) * (2 - (a : ℝ)) := by
  have hL : (∫ x, (1 - (a : ℝ) * (x 0 : ℝ)) ^ 2 * (1 - (a : ℝ) * (x 1 : ℝ)) ∂C.toMeasure) =
      1 - 3 * (a : ℝ) / 2 + (a : ℝ) ^ 2 / 3 +
        2 * (a : ℝ) ^ 2 * (∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂C.toMeasure) -
        (a : ℝ) ^ 3 * (∫ x, (x 0 : ℝ) ^ 2 * (x 1 : ℝ) ∂C.toMeasure) := by
    have he : (fun x : Fin 2 → I => (1 - (a : ℝ) * (x 0 : ℝ)) ^ 2 * (1 - (a : ℝ) * (x 1 : ℝ))) =
        fun x => 1 - (2 * (a : ℝ)) * (x 0 : ℝ) - (a : ℝ) * (x 1 : ℝ) +
          (a : ℝ) ^ 2 * (x 0 : ℝ) ^ 2 + (2 * (a : ℝ) ^ 2) * ((x 0 : ℝ) * (x 1 : ℝ)) -
          (a : ℝ) ^ 3 * ((x 0 : ℝ) ^ 2 * (x 1 : ℝ)) := by funext x; ring
    rw [he, integral_sub, integral_add, integral_add, integral_sub, integral_sub]
    · rw [integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
        C.integral_coe_eval, C.integral_coe_eval, C.integral_sq_eval]
      norm_num
      ring
    all_goals exact Copula.integrable_continuous_cube _ (by fun_prop)
  have hU : (∫ x, (1 - ((a : ℝ) + (1 - (a : ℝ)) * (x 0 : ℝ))) ^ 2 *
      (1 - ((a : ℝ) + (1 - (a : ℝ)) * (x 1 : ℝ))) ∂D.toMeasure) =
      (1 - (a : ℝ)) ^ 3 * (∫ x, (1 - (x 0 : ℝ)) ^ 2 * (1 - (x 1 : ℝ)) ∂D.toMeasure) := by
    have he : (fun x : Fin 2 → I => (1 - ((a : ℝ) + (1 - (a : ℝ)) * (x 0 : ℝ))) ^ 2 *
        (1 - ((a : ℝ) + (1 - (a : ℝ)) * (x 1 : ℝ)))) =
        fun x => (1 - (a : ℝ)) ^ 3 * ((1 - (x 0 : ℝ)) ^ 2 * (1 - (x 1 : ℝ))) := by funext x; ring
    rw [he, integral_const_mul]
  have hr : 12 * (∫ x, (x 0 : ℝ) * (x 1 : ℝ) ∂C.toMeasure) = C.spearmanRho + 3 := by
    rw [Copula.spearmanRho]
    ring
  have hn := raw_blest_moment C
  have hd := nu_moment D
  rw [nu_moment, Copula.integral_ordinalSum _ _ _ (by fun_prop)]
  simp only [Copula.OrdinalSum.lowerEmbed, Copula.OrdinalSum.upperEmbed]
  rw [hL, hU]
  linear_combination 2 * (a : ℝ) ^ 3 * hr - (a : ℝ) ^ 4 * hn - (1 - (a : ℝ)) ^ 4 * hd

def halfRotation : Copula 2 :=
  (Copula.countermonotonic.ordinalSum Copula.countermonotonic Copula.unitHalf).reflect {0}

theorem halfRotation_values :
    blestNu halfRotation = -1 / 2 ∧ halfRotation.spearmanRho = -1 / 2 ∧ halfRotation.blomqvistBeta = -1 := by
  have hn : blestNu halfRotation = -1 / 2 := by
    rw [halfRotation, nu_reflect_first, blest_ordinalSum, Copula.spearmanRho_ordinalSum,
      blest_countermonotonic, Copula.spearmanRho_countermonotonic]
    norm_num [Copula.unitHalf]
  have hr : halfRotation.spearmanRho = -1 / 2 := by
    rw [halfRotation, Copula.spearmanRho_reflect_first, Copula.spearmanRho_ordinalSum,
      Copula.spearmanRho_countermonotonic]
    norm_num [Copula.unitHalf]
  have hb : halfRotation.blomqvistBeta = -1 := by
    rw [halfRotation, Copula.blomqvistBeta_reflect_first, Copula.blomqvistBeta,
      Copula.cdf_ordinalSum_split]
    norm_num [Copula.unitHalf]
  exact ⟨hn, hr, hb⟩

def betaWitness : Copula 2 := Verification.centeredOrdinal halfRotation ⟨2 / 3, by norm_num⟩

/-- The upper extremizer P_(1/6), assembled from its three ordinal blocks. -/
theorem betaWitness_values : blestNu betaWitness = 5 / 9 ∧ betaWitness.blomqvistBeta = -1 / 3 := by
  constructor
  · unfold betaWitness Verification.centeredOrdinal
    rw [blest_ordinalSum, blest_ordinalSum, Copula.spearmanRho_comonotonic,
      blest_comonotonic, halfRotation_values.1, halfRotation_values.2.1]
    norm_num [Verification.centralMargin, Verification.centralSplit]
  · rw [betaWitness, Verification.centeredOrdinal_beta, halfRotation_values.2.2]
    norm_num

theorem nu_beta_upper_attained : ∃ C : Copula 2, blestNu C - C.blomqvistBeta = 8 / 9 := by
  refine ⟨betaWitness, ?_⟩
  rw [betaWitness_values.1, betaWitness_values.2]
  norm_num

theorem nu_beta_lower_attained : ∃ C : Copula 2, blestNu C - C.blomqvistBeta = -8 / 9 := by
  refine ⟨betaWitness.reflect {1}, ?_⟩
  rw [blest_reflect_second, Copula.blomqvistBeta_reflect_second, betaWitness_values.1, betaWitness_values.2]
  norm_num

#assert_standard_axioms Papers.Rockel2026ExactBlest.raw_blest_moment
#assert_standard_axioms Papers.Rockel2026ExactBlest.blest_ordinalSum
#assert_standard_axioms Papers.Rockel2026ExactBlest.halfRotation_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.betaWitness_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_upper_attained
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_beta_lower_attained

end
end Papers.Rockel2026ExactBlest
