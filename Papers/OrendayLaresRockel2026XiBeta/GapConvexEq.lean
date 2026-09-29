import Papers.OrendayLaresRockel2026XiBeta.GapConvex

/-! # Lemma 5.2: the equality case

`J(w) = 2 q²` holds iff `w = max {|u - 1/2|, q}` on `[0,1]`.
-/

open MeasureTheory Set intervalIntegral

namespace Papers.OrendayLaresRockel2026XiBeta

theorem integral_eq_of_eq_on_Ioo {f : ℝ → ℝ} {c d k : ℝ} (hcd : c ≤ d)
    (h : ∀ t ∈ Ioo c d, f t = k) : ∫ t in c..d, f t = (d - c) * k := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => k)]
  · simp
  · have hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ({d} : Set ℝ) :=
      (Set.countable_singleton d).ae_notMem volume
    filter_upwards [hd] with t ht hmem
    rw [uIoc_of_le hcd] at hmem
    exact h t ⟨hmem.1, lt_of_le_of_ne hmem.2 (by simpa using ht)⟩

namespace SlopeData

variable (S : SlopeData)

theorem abs_w_sub_q_le {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : |S.w u - S.q| ≤ |u - 1 / 2| := by
  unfold q
  rcases le_total u (1 / 2) with h | h
  · rw [abs_sub_comm, abs_sub_comm u]
    rw [abs_of_nonneg (by linarith : 0 ≤ 1 / 2 - u)]
    exact S.w_sub_le hu.1 h (by norm_num)
  · rw [abs_of_nonneg (by linarith : 0 ≤ u - 1 / 2)]
    exact S.w_sub_le (by norm_num) h hu.2

/-- Lemma 5.2, equality: `J(w) = 2 q²` forces `w = max {|u - 1/2|, q}`. -/
theorem eq_max_of_J_eq (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u)
    (hJ : S.J = 2 * S.q ^ 2) : ∀ u ∈ Icc (0 : ℝ) 1, S.w u = max |u - 1 / 2| S.q := by
  intro u hu
  rcases (S.q_nonneg hw).eq_or_lt with h0 | hpos
  · have h1 := S.abs_w_sub_q_le hu
    have h2 := hw u hu
    rw [← h0] at h1 ⊢
    rw [max_eq_left (abs_nonneg _)]
    rw [abs_le] at h1
    linarith [h1.2]
  · obtain ⟨ΔX, ΔY, E, hX, hY, hE, hXd, hYd, hEd, h⟩ := S.J_slack hw hpos
    have habs := S.abs_m_le
    rw [abs_le] at habs
    have ha : 0 < 1 + S.d (1 / 2) := by linarith [habs.1]
    have hc : 0 < 1 - S.d (1 / 2) := by linarith [habs.2]
    have hcX := mul_nonneg hc.le hX
    have haY := mul_nonneg ha.le hY
    have hX0 : ΔX = 0 := by
      have : (1 - S.d (1 / 2)) * ΔX = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc.ne'
      · exact h
    have hY0 : ΔY = 0 := by
      have : (1 + S.d (1 / 2)) * ΔY = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ha.ne'
      · exact h
    have hE0 : E = 0 := by linarith
    have hm : S.d (1 / 2) = 0 := by
      rw [hE0] at hEd
      have h1 : 2 * S.q ^ 2 * S.d (1 / 2) ^ 2 = 0 := by
        have := hEd.symm
        rw [div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h (mul_pos ha hc).ne'
      have h2 : S.d (1 / 2) ^ 2 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact absurd h (by positivity)
        · exact h
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
    obtain ⟨⟨-, hXeq⟩, ⟨-, hYeq⟩⟩ := S.areas hw hpos
    rw [hm] at hXeq hYeq
    have hXeq' := hXeq (by rw [hm] at hXd; linarith)
    have hYeq' := hYeq (by rw [hm] at hYd; linarith)
    rcases le_total u (1 / 2) with hle | hle
    · have := hXeq' u ⟨hu.1, hle⟩
      rw [this, abs_of_nonpos (by linarith)]
      simp
    · have := hYeq' u ⟨hle, hu.2⟩
      rw [this, abs_of_nonneg (by linarith)]
      simp

section converse

variable (hg : ∀ u ∈ Icc (0 : ℝ) 1, S.w u = max |u - 1 / 2| S.q)
  (hq0 : 0 ≤ S.q) (hq1 : 2 * S.q ≤ 1)

include hg hq0 hq1

theorem d_left {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2 - S.q) : S.d c = -1 := by
  have hb : (1 / 2 - S.q) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hc1 : c ∈ Icc (0 : ℝ) 1 := ⟨hc0, by linarith⟩
  have wb : S.w (1 / 2 - S.q) = S.q := by
    rw [hg _ hb, show (1 / 2 - S.q) - 1 / 2 = -S.q by ring, abs_neg, abs_of_nonneg hq0, max_self]
  have wc : S.w c = 1 / 2 - c := by
    rw [hg _ hc1, abs_of_nonpos (by linarith)]
    have : S.q ≤ -(c - 1 / 2) := by linarith
    rw [max_eq_left this]; ring
  have hint := S.w_sub c (1 / 2 - S.q)
  have hmono : ∫ t in c..(1 / 2 - S.q), S.d c ≤ ∫ t in c..(1 / 2 - S.q), S.d t :=
    integral_mono_on hc.le intervalIntegrable_const (S.ii _ _) (fun t ht => S.mono ht.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [← hint, wb, wc] at hmono
  have := S.d_ge hc1
  have hpos : 0 < 1 / 2 - S.q - c := by linarith
  nlinarith

theorem d_mid {c : ℝ} (hc : c ∈ Ioo (1 / 2 - S.q) (1 / 2 + S.q)) : S.d c = 0 := by
  have hc1 : c ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
  have ha : (1 / 2 - S.q) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hb : (1 / 2 + S.q) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have wa : S.w (1 / 2 - S.q) = S.q := by
    rw [hg _ ha, show (1 / 2 - S.q) - 1 / 2 = -S.q by ring, abs_neg, abs_of_nonneg hq0, max_self]
  have wb : S.w (1 / 2 + S.q) = S.q := by
    rw [hg _ hb, show (1 / 2 + S.q) - 1 / 2 = S.q by ring, abs_of_nonneg hq0, max_self]
  have wc : S.w c = S.q := by
    rw [hg _ hc1]
    apply max_eq_right
    rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
  have h1 : ∫ t in (1 / 2 - S.q)..c, S.d t ≤ ∫ t in (1 / 2 - S.q)..c, S.d c :=
    integral_mono_on hc.1.le (S.ii _ _) intervalIntegrable_const (fun t ht => S.mono ht.2)
  have h2 : ∫ t in c..(1 / 2 + S.q), S.d c ≤ ∫ t in c..(1 / 2 + S.q), S.d t :=
    integral_mono_on hc.2.le intervalIntegrable_const (S.ii _ _) (fun t ht => S.mono ht.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
  rw [← S.w_sub, wc, wa] at h1
  rw [← S.w_sub, wc, wb] at h2
  have p1 : 0 < c - (1 / 2 - S.q) := by linarith [hc.1]
  have p2 : 0 < 1 / 2 + S.q - c := by linarith [hc.2]
  apply le_antisymm
  · nlinarith
  · nlinarith

theorem d_right {c : ℝ} (hc : 1 / 2 + S.q < c) (hc1 : c ≤ 1) : S.d c = 1 := by
  have hc1' : c ∈ Icc (0 : ℝ) 1 := ⟨by linarith, hc1⟩
  have ha : (1 / 2 + S.q) ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have wa : S.w (1 / 2 + S.q) = S.q := by
    rw [hg _ ha, show (1 / 2 + S.q) - 1 / 2 = S.q by ring, abs_of_nonneg hq0, max_self]
  have wc : S.w c = c - 1 / 2 := by
    rw [hg _ hc1', abs_of_nonneg (by linarith)]
    exact max_eq_left (by linarith : S.q ≤ c - 1 / 2)
  have h1 : ∫ t in (1 / 2 + S.q)..c, S.d t ≤ ∫ t in (1 / 2 + S.q)..c, S.d c :=
    integral_mono_on hc.le (S.ii _ _) intervalIntegrable_const (fun t ht => S.mono ht.2)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1
  rw [← S.w_sub, wc, wa] at h1
  have p1 : 0 < c - (1 / 2 + S.q) := by linarith
  have := S.d_le hc1'
  nlinarith

/-- Lemma 5.2, equality (converse): `w = max {|u - 1/2|, q}` gives `J(w) = 2 q²`. -/
theorem J_eq_of_eq_max : S.J = 2 * S.q ^ 2 := by
  have hc1 : 0 ≤ 1 / 2 - S.q := by linarith
  have hc12 : 1 / 2 - S.q ≤ 1 / 2 + S.q := by linarith
  have hc2 : 1 / 2 + S.q ≤ 1 := by linarith
  unfold J
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2 - S.q)
      (S.ii_F (le_refl 0) hc1 (by linarith)) (S.ii_F hc1 (by linarith) (by linarith)),
    ← intervalIntegral.integral_add_adjacent_intervals (a := 1 / 2 - S.q) (b := 1 / 2 + S.q)
      (S.ii_F hc1 hc12 (by linarith)) (S.ii_F (by linarith) hc2 (le_refl 1)),
    integral_eq_of_eq_on_Ioo hc1 (k := 0) (fun t ht => by
      rw [S.d_left hg hq0 hq1 ht.1.le ht.2]; ring),
    integral_eq_of_eq_on_Ioo hc12 (k := S.q) (fun t ht => by
      rw [S.d_mid hg hq0 hq1 ht, hg t ⟨by linarith [ht.1], by linarith [ht.2]⟩,
        max_eq_right (by rw [abs_le]; constructor <;> linarith [ht.1, ht.2])]
      ring),
    integral_eq_of_eq_on_Ioo hc2 (k := 0) (fun t ht => by
      rw [S.d_right hg hq0 hq1 ht.1 ht.2.le]; ring)]
  ring

end converse

/-- **Lemma 5.2**: `J(w) = 2 q²` if and only if `w = max {|u - 1/2|, q}` on `[0,1]`. -/
theorem J_eq_two_q_sq_iff (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u) :
    S.J = 2 * S.q ^ 2 ↔ ∀ u ∈ Icc (0 : ℝ) 1, S.w u = max |u - 1 / 2| S.q :=
  ⟨S.eq_max_of_J_eq hw, fun h => S.J_eq_of_eq_max h (S.q_nonneg hw) S.two_q_le_one⟩

end SlopeData

end Papers.OrendayLaresRockel2026XiBeta
