import Papers.OrendayLaresRockel2026XiBeta.RBranchBasic
import Copula.OrdinalSum.Finite

/-! # `R_0` and the ordinal-sum structure of `R_b` (Proposition 5.3 (ii))

For `0 < b < 1`, `R_b` is the ordinal sum of `M`, `R_0`, `M` with respect to the partition
`{[0, b/2], [b/2, 1 - b/2], [1 - b/2, 1]}` (`Copula.finiteOrdinalSum`).
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

theorem zero_mem_Icc01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, zero_le_one⟩

/-- `R_0`: `R_0(u, v) = min (u/2, v)` for `v ≤ 1/2` and `min (u, u/2 + v - 1/2)` for `v ≥ 1/2`. -/
theorem Rb_zero_cdf_of_le_half (u v : I) (hv : (v : ℝ) ≤ 1 / 2) :
    (Rb 0 zero_mem_Icc01).cdf ![u, v] = min ((u : ℝ) / 2) v := by
  rw [Rb_cdf_of_le_half _ u v hv]
  have hu := u.2
  unfold rbA
  simp only [min_def]
  split_ifs <;> linarith [hu.1, hu.2]

theorem Rb_zero_cdf_of_half_le (u v : I) (hv : 1 / 2 ≤ (v : ℝ)) :
    (Rb 0 zero_mem_Icc01).cdf ![u, v] = min (u : ℝ) ((u : ℝ) / 2 + v - 1 / 2) := by
  rw [Rb_cdf_of_half_le _ u v hv]
  have hu := u.2
  unfold rbA
  simp only [min_def]
  split_ifs <;> linarith [hu.1, hu.2]

/-- The partition `{[0, b/2], [b/2, 1 - b/2], [1 - b/2, 1]}`. -/
noncomputable def rbPartition (b : ℝ) (h0 : 0 < b) (h1 : b < 1) : Copula.IntervalPartition 3 where
  point := ![0, ⟨b / 2, by linarith, by linarith⟩, ⟨1 - b / 2, by linarith, by linarith⟩, 1]
  strictMono := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    · change ((0 : I) : ℝ) < b / 2
      simp only [Set.Icc.coe_zero]; linarith
    · change b / 2 < 1 - b / 2
      linarith
    · change 1 - b / 2 < ((1 : I) : ℝ)
      simp only [Set.Icc.coe_one]; linarith
  zero := rfl
  one := rfl

theorem rbPartition_point_one (b : ℝ) (h0 : 0 < b) (h1 : b < 1) :
    (((rbPartition b h0 h1).point 1 : I) : ℝ) = b / 2 := rfl

theorem rbPartition_point_two (b : ℝ) (h0 : 0 < b) (h1 : b < 1) :
    (((rbPartition b h0 h1).point 2 : I) : ℝ) = 1 - b / 2 := rfl

theorem Rb_cdf_of_le_half_or {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (u v : I) :
    (Rb b hb).cdf ![u, v] =
      if (v : ℝ) ≤ 1 / 2 then min (rbA b u) v else min (u : ℝ) (rbA b u + v - 1 / 2) := by
  split_ifs with h
  · exact Rb_cdf_of_le_half hb u v h
  · exact Rb_cdf_of_half_le hb u v (not_le.mp h).le

/-- The real-variable identity behind the ordinal-sum decomposition (one zone). -/
noncomputable def ordLhs (b u v : ℝ) : ℝ :=
  if v ≤ 1 / 2 then min (rbA b u) v else min u (rbA b u + v - 1 / 2)

noncomputable def ordRhs (b u v : ℝ) : ℝ :=
  min (min u (b / 2) - min u 0) (min v (b / 2) - min v 0) +
        (if min v (1 - b / 2) - min v (b / 2) ≤ (1 - b) / 2 then
          min ((min u (1 - b / 2) - min u (b / 2)) / 2) (min v (1 - b / 2) - min v (b / 2))
        else min (min u (1 - b / 2) - min u (b / 2))
          ((min u (1 - b / 2) - min u (b / 2)) / 2 + (min v (1 - b / 2) - min v (b / 2)) - (1 - b) / 2))
      + min (min u 1 - min u (1 - b / 2)) (min v 1 - min v (1 - b / 2))

theorem ordinal_real_00 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : u ≤ b / 2) (h1 : v ≤ b / 2) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = u := by
    exact min_eq_left (by linarith)
  have mu2 : min u (1 - b / 2) = u := by
    exact min_eq_left (by linarith)
  have mv1 : min v (b / 2) = v := by
    exact min_eq_left (by linarith)
  have mv2 : min v (1 - b / 2) = v := by
    exact min_eq_left (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = u := by
    exact min_eq_left (by linarith)
  have mA2 : min (u) (1 / 2) = u := by
    exact min_eq_left (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real_01 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : u ≤ b / 2) (h1 : b / 2 ≤ v) (h2 : v ≤ 1 - b / 2) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = u := by
    exact min_eq_left (by linarith)
  have mu2 : min u (1 - b / 2) = u := by
    exact min_eq_left (by linarith)
  have mv1 : min v (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mv2 : min v (1 - b / 2) = v := by
    exact min_eq_left (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = u := by
    exact min_eq_left (by linarith)
  have mA2 : min (u) (1 / 2) = u := by
    exact min_eq_left (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real_02 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : u ≤ b / 2) (h1 : 1 - b / 2 ≤ v) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = u := by
    exact min_eq_left (by linarith)
  have mu2 : min u (1 - b / 2) = u := by
    exact min_eq_left (by linarith)
  have mv1 : min v (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mv2 : min v (1 - b / 2) = 1 - b / 2 := by
    exact min_eq_right (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = u := by
    exact min_eq_left (by linarith)
  have mA2 : min (u) (1 / 2) = u := by
    exact min_eq_left (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real_10 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : b / 2 ≤ u) (h1 : u ≤ 1 - b / 2) (h2 : v ≤ b / 2) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mu2 : min u (1 - b / 2) = u := by
    exact min_eq_left (by linarith)
  have mv1 : min v (b / 2) = v := by
    exact min_eq_left (by linarith)
  have mv2 : min v (1 - b / 2) = v := by
    exact min_eq_left (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = (2 * u + b) / 4 := by
    exact min_eq_right (by linarith)
  have mA2 : min ((2 * u + b) / 4) (1 / 2) = (2 * u + b) / 4 := by
    exact min_eq_left (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real_11 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : b / 2 ≤ u) (h1 : u ≤ 1 - b / 2) (h2 : b / 2 ≤ v) (h3 : v ≤ 1 - b / 2) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mu2 : min u (1 - b / 2) = u := by
    exact min_eq_left (by linarith)
  have mv1 : min v (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mv2 : min v (1 - b / 2) = v := by
    exact min_eq_left (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = (2 * u + b) / 4 := by
    exact min_eq_right (by linarith)
  have mA2 : min ((2 * u + b) / 4) (1 / 2) = (2 * u + b) / 4 := by
    exact min_eq_left (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real_12 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : b / 2 ≤ u) (h1 : u ≤ 1 - b / 2) (h2 : 1 - b / 2 ≤ v) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mu2 : min u (1 - b / 2) = u := by
    exact min_eq_left (by linarith)
  have mv1 : min v (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mv2 : min v (1 - b / 2) = 1 - b / 2 := by
    exact min_eq_right (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = (2 * u + b) / 4 := by
    exact min_eq_right (by linarith)
  have mA2 : min ((2 * u + b) / 4) (1 / 2) = (2 * u + b) / 4 := by
    exact min_eq_left (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real_20 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : 1 - b / 2 ≤ u) (h1 : v ≤ b / 2) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mu2 : min u (1 - b / 2) = 1 - b / 2 := by
    exact min_eq_right (by linarith)
  have mv1 : min v (b / 2) = v := by
    exact min_eq_left (by linarith)
  have mv2 : min v (1 - b / 2) = v := by
    exact min_eq_left (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = (2 * u + b) / 4 := by
    exact min_eq_right (by linarith)
  have mA2 : min ((2 * u + b) / 4) (1 / 2) = 1 / 2 := by
    exact min_eq_right (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real_21 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : 1 - b / 2 ≤ u) (h1 : b / 2 ≤ v) (h2 : v ≤ 1 - b / 2) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mu2 : min u (1 - b / 2) = 1 - b / 2 := by
    exact min_eq_right (by linarith)
  have mv1 : min v (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mv2 : min v (1 - b / 2) = v := by
    exact min_eq_left (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = (2 * u + b) / 4 := by
    exact min_eq_right (by linarith)
  have mA2 : min ((2 * u + b) / 4) (1 / 2) = 1 / 2 := by
    exact min_eq_right (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

set_option maxHeartbeats 600000 in
theorem ordinal_real_22 {b u v : ℝ} (_hb0 : 0 ≤ b) (_hb1 : b ≤ 1) (_h0 : 0 < b) (_h1 : b < 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (h0 : 1 - b / 2 ≤ u) (h1 : 1 - b / 2 ≤ v) :
    ordLhs b u v = ordRhs b u v := by
  have m1u : min u 0 = 0 := min_eq_right hu0
  have m1v : min v 0 = 0 := min_eq_right hv0
  have m2u : min u 1 = u := min_eq_left hu1
  have m2v : min v 1 = v := min_eq_left hv1
  have mu1 : min u (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mu2 : min u (1 - b / 2) = 1 - b / 2 := by
    exact min_eq_right (by linarith)
  have mv1 : min v (b / 2) = b / 2 := by
    exact min_eq_right (by linarith)
  have mv2 : min v (1 - b / 2) = 1 - b / 2 := by
    exact min_eq_right (by linarith)
  have mA1 : min u ((2 * u + b) / 4) = (2 * u + b) / 4 := by
    exact min_eq_right (by linarith)
  have mA2 : min ((2 * u + b) / 4) (1 / 2) = 1 / 2 := by
    exact min_eq_right (by linarith)
  unfold ordLhs ordRhs rbA
  rw [m1u, m1v, m2u, m2v, mu1, mu2, mv1, mv2, mA1, mA2]
  clear m1u m1v m2u m2v mu1 mu2 mv1 mv2 mA1 mA2
  split_ifs <;> simp only [min_def] <;> split_ifs <;> linarith

theorem ordinal_real {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (h0 : 0 < b) (h1 : b < 1)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    ordLhs b u v = ordRhs b u v := by
  obtain ⟨hu0, hu1⟩ := hu
  obtain ⟨hv0, hv1⟩ := hv
  rcases le_total u (b / 2) with a1 | a1
  · rcases le_total v (b / 2) with c1 | c1
    · exact ordinal_real_00 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a1 c1
    · rcases le_total v (1 - b / 2) with c2 | c2
      · exact ordinal_real_01 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a1 c1 c2
      · exact ordinal_real_02 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a1 c2
  · rcases le_total u (1 - b / 2) with a2 | a2
    · rcases le_total v (b / 2) with c1 | c1
      · exact ordinal_real_10 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a1 a2 c1
      · rcases le_total v (1 - b / 2) with c2 | c2
        · exact ordinal_real_11 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a1 a2 c1 c2
        · exact ordinal_real_12 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a1 a2 c2
    · rcases le_total v (b / 2) with c1 | c1
      · exact ordinal_real_20 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a2 c1
      · rcases le_total v (1 - b / 2) with c2 | c2
        · exact ordinal_real_21 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a2 c1 c2
        · exact ordinal_real_22 hb0 hb1 h0 h1 hu0 hu1 hv0 hv1 a2 c2

/-- **Proposition 5.3 (ii)**: for `0 < b < 1`, `R_b` is the ordinal sum of `M`, `R_0`, `M` with
respect to the partition `{[0, b/2], [b/2, 1 - b/2], [1 - b/2, 1]}`. -/
theorem Rb_eq_finiteOrdinalSum {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (h0 : 0 < b) (h1 : b < 1) :
    Rb b hb = Copula.finiteOrdinalSum (rbPartition b h0 h1)
      ![Copula.comonotonic 2, Rb 0 zero_mem_Icc01, Copula.comonotonic 2] := by
  set P := rbPartition b h0 h1 with hP
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_finiteOrdinalSum, Fin.sum_univ_three]
  have p0 : (P.point (0 : Fin 3).castSucc : ℝ) = 0 := rfl
  have p1 : (P.point (0 : Fin 3).succ : ℝ) = b / 2 := rfl
  have p1' : (P.point (1 : Fin 3).castSucc : ℝ) = b / 2 := rfl
  have p2 : (P.point (1 : Fin 3).succ : ℝ) = 1 - b / 2 := rfl
  have p2' : (P.point (2 : Fin 3).castSucc : ℝ) = 1 - b / 2 := rfl
  have p3 : (P.point (2 : Fin 3).succ : ℝ) = 1 := rfl
  have wM : ∀ i : Fin 3, P.width i * (Copula.comonotonic 2).cdf ![P.coord i u, P.coord i v] =
      min (min (u : ℝ) (P.point i.succ) - min (u : ℝ) (P.point i.castSucc))
        (min (v : ℝ) (P.point i.succ) - min (v : ℝ) (P.point i.castSucc)) := by
    intro i
    rw [Copula.cdf_comonotonic_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_min_of_nonneg _ _ (P.width_pos i).le, P.width_mul_coord, P.width_mul_coord]
  have wR : P.width 1 * (Rb 0 zero_mem_Icc01).cdf ![P.coord 1 u, P.coord 1 v] =
      if min (v : ℝ) (1 - b / 2) - min (v : ℝ) (b / 2) ≤ (1 - b) / 2 then
        min ((min (u : ℝ) (1 - b / 2) - min (u : ℝ) (b / 2)) / 2)
          (min (v : ℝ) (1 - b / 2) - min (v : ℝ) (b / 2))
      else min (min (u : ℝ) (1 - b / 2) - min (u : ℝ) (b / 2))
        ((min (u : ℝ) (1 - b / 2) - min (u : ℝ) (b / 2)) / 2 +
          (min (v : ℝ) (1 - b / 2) - min (v : ℝ) (b / 2)) - (1 - b) / 2) := by
    have hw : P.width 1 = 1 - b := by
      unfold Copula.IntervalPartition.width
      rw [p2, p1']; ring
    have hu := P.width_mul_coord 1 u
    have hv := P.width_mul_coord 1 v
    rw [p2, p1'] at hu hv
    rw [hw] at hu hv ⊢
    by_cases hc : ((P.coord 1 v : I) : ℝ) ≤ 1 / 2
    · have hY : min (v : ℝ) (1 - b / 2) - min (v : ℝ) (b / 2) ≤ (1 - b) / 2 := by
        rw [← hv]; nlinarith
      rw [Rb_zero_cdf_of_le_half _ _ hc]
      simp only [hY, ↓reduceIte]
      rw [mul_min_of_nonneg _ _ (by linarith)]
      congr 1
      linarith
    · push Not at hc
      have hY : ¬ (min (v : ℝ) (1 - b / 2) - min (v : ℝ) (b / 2) ≤ (1 - b) / 2) := by
        rw [← hv]; nlinarith
      rw [Rb_zero_cdf_of_half_le _ _ hc.le]
      simp only [hY, ↓reduceIte]
      rw [mul_min_of_nonneg _ _ (by linarith)]
      congr 1
      linarith
  have c0 : (![Copula.comonotonic 2, Rb 0 zero_mem_Icc01, Copula.comonotonic 2] : Fin 3 → Copula 2) 0 =
    Copula.comonotonic 2 := rfl
  have c1 : (![Copula.comonotonic 2, Rb 0 zero_mem_Icc01, Copula.comonotonic 2] : Fin 3 → Copula 2) 1 =
    Rb 0 zero_mem_Icc01 := rfl
  have c2 : (![Copula.comonotonic 2, Rb 0 zero_mem_Icc01, Copula.comonotonic 2] : Fin 3 → Copula 2) 2 =
    Copula.comonotonic 2 := rfl
  rw [c0, c1, c2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [wM 0, wR, wM 2, p0, p1, p2', p3]
  rw [Rb_cdf_of_le_half_or hb u v]
  exact ordinal_real hb.1 hb.2 h0 h1 u.2 v.2

end Papers.OrendayLaresRockel2026XiBeta
