import Papers.OrendayLaresRockel2026XiBeta.GapConvexAux
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-! # Lemma 5.2: a sharp inequality for convex functions

A convex function `w : [0,1] → ℝ` with `w(0) = w(1) = 1/2` and `w ≥ |u - 1/2|` is
`1`-Lipschitz, hence of the form `w(u) = 1/2 + ∫₀ᵘ d` for a nondecreasing slope `d` with
`|d| ≤ 1` (its one-sided derivative) and `∫₀¹ d = 0`.  We encode `w` through this slope
(`SlopeData`); the gap function of a median section is of this form with `d = 1 - 2p`.
The functional is `J(w) = ∫₀¹ w (1 - w'²)`.

Main results: `two_q_sq_le_J` (`J(w) ≥ 2 q²`, `q = w(1/2)`) and `J_eq_two_q_sq_iff`
(equality iff `w = max {|u - 1/2|, q}`).
-/

open MeasureTheory Set intervalIntegral

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The slope `d = w'` of a convex function `w` on `[0,1]` with `w(0) = w(1) = 1/2` that lies
in `[-1,1]`. -/
structure SlopeData where
  /-- the (nondecreasing) derivative -/
  d : ℝ → ℝ
  mono : Monotone d
  bdd : ∀ u ∈ Icc (0 : ℝ) 1, |d u| ≤ 1
  integral_zero : ∫ u in (0 : ℝ)..1, d u = 0

namespace SlopeData

variable (S : SlopeData)

/-- The convex function `w(u) = 1/2 + ∫₀ᵘ w'`. -/
noncomputable def w (u : ℝ) : ℝ := 1 / 2 + ∫ t in (0 : ℝ)..u, S.d t

/-- The functional `J(w) = ∫₀¹ w (1 - w'²)` of Lemma 5.2. -/
noncomputable def J : ℝ := ∫ u in (0 : ℝ)..1, S.w u * (1 - S.d u ^ 2)

/-- `q = w(1/2)`. -/
noncomputable def q : ℝ := S.w (1 / 2)

theorem ii (a b : ℝ) : IntervalIntegrable S.d volume a b := S.mono.intervalIntegrable

theorem w_sub (a b : ℝ) : S.w b - S.w a = ∫ t in a..b, S.d t := by
  unfold w
  rw [add_sub_add_left_eq_sub, integral_interval_sub_left (S.ii 0 b) (S.ii 0 a)]

theorem continuous_w : Continuous S.w :=
  continuous_const.add (intervalIntegral.continuous_primitive S.ii 0)

theorem w_zero : S.w 0 = 1 / 2 := by simp [w]

theorem w_one : S.w 1 = 1 / 2 := by simp [w, S.integral_zero]

theorem d_ge {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : -1 ≤ S.d u := (abs_le.1 (S.bdd u hu)).1

theorem d_le {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : S.d u ≤ 1 := (abs_le.1 (S.bdd u hu)).2

/-- `w` is `1`-Lipschitz on `[0,1]`. -/
theorem w_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |S.w b - S.w a| ≤ b - a := by
  rw [S.w_sub, abs_le]
  have h1 : ∫ t in a..b, (-1 : ℝ) ≤ ∫ t in a..b, S.d t :=
    integral_mono_on hab intervalIntegrable_const (S.ii _ _)
      (fun t ht => S.d_ge ⟨ha.trans ht.1, ht.2.trans hb⟩)
  have h2 : ∫ t in a..b, S.d t ≤ ∫ t in a..b, (1 : ℝ) :=
    integral_mono_on hab (S.ii _ _) intervalIntegrable_const
      (fun t ht => S.d_le ⟨ha.trans ht.1, ht.2.trans hb⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h1 h2
  constructor <;> linarith

/-- Supporting line of `w` at `1/2` with slope `m = d(1/2)`. -/
theorem w_support {u : ℝ} : S.q + S.d (1 / 2) * (u - 1 / 2) ≤ S.w u := by
  have h := S.w_sub (1 / 2) u
  unfold q
  rcases le_total (1 / 2) u with hu | hu
  · have : ∫ t in (1 / 2 : ℝ)..u, S.d (1 / 2) ≤ ∫ t in (1 / 2 : ℝ)..u, S.d t :=
      integral_mono_on hu intervalIntegrable_const (S.ii _ _) (fun t ht => S.mono ht.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have : ∫ t in u..(1 / 2 : ℝ), S.d t ≤ ∫ t in u..(1 / 2 : ℝ), S.d (1 / 2) :=
      integral_mono_on hu (S.ii _ _) intervalIntegrable_const (fun t ht => S.mono ht.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [intervalIntegral.integral_symm] at h
    linarith

/-- `d` is integrable against continuous functions, and `∫ w w' = [w²/2]`. -/
theorem integral_w_mul_d {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, S.w t * S.d t = (S.w b ^ 2 - S.w a ^ 2) / 2 := by
  have hcount : {x : ℝ | ¬ ContinuousAt S.d x}.Countable := S.mono.countable_not_continuousAt
  have hderiv : ∀ x ∈ Ioo a b \ {x : ℝ | ¬ ContinuousAt S.d x},
      HasDerivAt (fun t => S.w t ^ 2 / 2) (S.w x * S.d x) x := by
    intro x hx
    have hc : ContinuousAt S.d x := by simpa using hx.2
    have h1 : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, S.d t) (S.d x) x :=
      intervalIntegral.integral_hasDerivAt_right (S.ii 0 x)
        (S.mono.measurable.stronglyMeasurable.stronglyMeasurableAtFilter) hc
    have h2 : HasDerivAt S.w (S.d x) x := h1.const_add _
    have h3 := (h2.pow 2).div_const 2
    convert h3 using 1
    ring
  have := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le (fun t => S.w t ^ 2 / 2)
    (fun t => S.w t * S.d t) hab hcount
    ((S.continuous_w.pow 2).div_const 2).continuousOn hderiv
    ((S.ii a b).continuousOn_mul S.continuous_w.continuousOn)
  rw [this]; ring

theorem w_nonneg {u : ℝ} (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u)
    (hu : u ∈ Icc (0 : ℝ) 1) : 0 ≤ S.w u :=
  (abs_nonneg _).trans (hw u hu)

theorem q_nonneg (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u) : 0 ≤ S.q :=
  S.w_nonneg hw ⟨by norm_num, by norm_num⟩

/-- The slope at `1/2` satisfies `|m| ≤ 1 - 2q`; in particular `2q ≤ 1`. -/
theorem abs_m_le : |S.d (1 / 2)| ≤ 1 - 2 * S.q := by
  have h0 := S.w_support (u := 0)
  have h1 := S.w_support (u := 1)
  rw [S.w_zero] at h0
  rw [S.w_one] at h1
  rw [abs_le]; constructor <;> nlinarith

theorem two_q_le_one : 2 * S.q ≤ 1 := by
  have h0 := S.w_support (u := 0)
  have h1 := S.w_support (u := 1)
  rw [S.w_zero] at h0
  rw [S.w_one] at h1
  nlinarith

theorem ii_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun u => S.d u ^ 2) volume a b := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
  · exact (S.mono.measurable.pow_const 2).aestronglyMeasurable
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [uIoc_of_le hab] at hx
    have := S.bdd x ⟨ha.trans hx.1.le, hx.2.trans hb⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (S.d x), sq_abs (S.d x)]

theorem ii_F {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun u => S.w u * (1 - S.d u ^ 2)) volume a b :=
  (intervalIntegrable_const.sub (S.ii_sq ha hab hb)).continuousOn_mul S.continuous_w.continuousOn

theorem J_nonneg (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u) : 0 ≤ S.J := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro u hu
  refine mul_nonneg (S.w_nonneg hw hu) ?_
  have := S.bdd u hu
  nlinarith [abs_nonneg (S.d u), sq_abs (S.d u)]

/-- The first two lower bounds in the proof of Lemma 5.2. -/
theorem J_ge (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u) :
    (1 - S.d (1 / 2)) * ((∫ u in (0 : ℝ)..(1 / 2), S.w u) + S.q ^ 2 / 2 - 1 / 8) +
      (1 + S.d (1 / 2)) * ((∫ u in (1 / 2 : ℝ)..1, S.w u) - 1 / 8 + S.q ^ 2 / 2) ≤ S.J := by
  set m := S.d (1 / 2) with hm
  have hwc : ∀ a b : ℝ, IntervalIntegrable S.w volume a b :=
    fun a b => S.continuous_w.intervalIntegrable a b
  have hwd : ∀ a b : ℝ, IntervalIntegrable (fun u => S.w u * S.d u) volume a b :=
    fun a b => (S.ii a b).continuousOn_mul S.continuous_w.continuousOn
  have hL : (1 - m) * ((∫ u in (0 : ℝ)..(1 / 2), S.w u) + S.q ^ 2 / 2 - 1 / 8) ≤
      ∫ u in (0 : ℝ)..(1 / 2), S.w u * (1 - S.d u ^ 2) := by
    have e : ∫ u in (0 : ℝ)..(1 / 2), (1 - m) * (S.w u + S.w u * S.d u) =
        (1 - m) * ((∫ u in (0 : ℝ)..(1 / 2), S.w u) + S.q ^ 2 / 2 - 1 / 8) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hwc _ _) (hwd _ _),
        S.integral_w_mul_d (by norm_num), S.w_zero]
      unfold q; ring
    rw [← e]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((hwc _ _).add (hwd _ _)).const_mul _
    · exact S.ii_F (le_refl 0) (by norm_num) (by norm_num)
    · intro u hu
      have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.trans (by norm_num)⟩
      have h0 := S.w_nonneg hw hu1
      have h1 := S.d_ge hu1
      have h2 : S.d u ≤ m := S.mono hu.2
      have : S.w u * (1 - S.d u ^ 2) - (1 - m) * (S.w u + S.w u * S.d u) =
          S.w u * (1 + S.d u) * (m - S.d u) := by ring
      nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : 0 ≤ 1 + S.d u)) (sub_nonneg.2 h2)]
  have hR : (1 + m) * ((∫ u in (1 / 2 : ℝ)..1, S.w u) - 1 / 8 + S.q ^ 2 / 2) ≤
      ∫ u in (1 / 2 : ℝ)..1, S.w u * (1 - S.d u ^ 2) := by
    have e : ∫ u in (1 / 2 : ℝ)..1, (1 + m) * (S.w u - S.w u * S.d u) =
        (1 + m) * ((∫ u in (1 / 2 : ℝ)..1, S.w u) - 1 / 8 + S.q ^ 2 / 2) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hwc _ _) (hwd _ _),
        S.integral_w_mul_d (by norm_num), S.w_one]
      unfold q; ring
    rw [← e]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact ((hwc _ _).sub (hwd _ _)).const_mul _
    · exact S.ii_F (by norm_num) (by norm_num) (le_refl 1)
    · intro u hu
      have hu1 : u ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hu.1], hu.2⟩
      have h0 := S.w_nonneg hw hu1
      have h1 := S.d_le hu1
      have h2 : m ≤ S.d u := S.mono hu.1
      have : S.w u * (1 - S.d u ^ 2) - (1 + m) * (S.w u - S.w u * S.d u) =
          S.w u * (1 - S.d u) * (S.d u - m) := by ring
      nlinarith [mul_nonneg (mul_nonneg h0 (by linarith : 0 ≤ 1 - S.d u)) (sub_nonneg.2 h2)]
  have hsplit : S.J = (∫ u in (0 : ℝ)..(1 / 2), S.w u * (1 - S.d u ^ 2)) +
      ∫ u in (1 / 2 : ℝ)..1, S.w u * (1 - S.d u ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (S.ii_F (le_refl 0) (by norm_num) (by norm_num))
      (S.ii_F (by norm_num) (by norm_num) (le_refl 1))).symm
  linarith

/-- The two triangle-area bounds (5.4) of Lemma 5.2, with their equality cases. -/
theorem areas (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u) (hq : 0 < S.q) :
    (1 / 8 + S.q ^ 2 / (2 * (1 + S.d (1 / 2))) ≤ ∫ u in (0 : ℝ)..(1 / 2), S.w u ∧
      (∫ u in (0 : ℝ)..(1 / 2), S.w u = 1 / 8 + S.q ^ 2 / (2 * (1 + S.d (1 / 2))) →
        ∀ u ∈ Icc (0 : ℝ) (1 / 2),
          S.w u = max (1 / 2 - u) (S.q + S.d (1 / 2) * (u - 1 / 2)))) ∧
    (1 / 8 + S.q ^ 2 / (2 * (1 - S.d (1 / 2))) ≤ ∫ u in (1 / 2 : ℝ)..1, S.w u ∧
      (∫ u in (1 / 2 : ℝ)..1, S.w u = 1 / 8 + S.q ^ 2 / (2 * (1 - S.d (1 / 2))) →
        ∀ u ∈ Icc (1 / 2 : ℝ) 1,
          S.w u = max (u - 1 / 2) (S.q + S.d (1 / 2) * (u - 1 / 2)))) := by
  have habs := S.abs_m_le
  rw [abs_le] at habs
  refine ⟨area_left S.continuous_w hq.le (by linarith [habs.1]) (by linarith [habs.1])
    (fun u hu => by
      have := hw u ⟨hu.1, hu.2.trans (by norm_num)⟩
      rw [abs_of_nonpos (by linarith [hu.2])] at this
      linarith)
    (fun u _ => S.w_support),
    area_right S.continuous_w hq.le (by linarith [habs.2]) (by linarith [habs.2])
    (fun u hu => by
      have := hw u ⟨by linarith [hu.1], hu.2⟩
      rw [abs_of_nonneg (by linarith [hu.1])] at this
      linarith)
    (fun u _ => S.w_support)⟩

/-- Everything Lemma 5.2 extracts from the two triangle areas when `q > 0`:
slacks `ΔX, ΔY ≥ 0` and the AM-GM defect `E ≥ 0`, with `c ΔX + a ΔY + E ≤ J - 2 q²`. -/
theorem J_slack (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u) (hq : 0 < S.q) :
    ∃ ΔX ΔY E : ℝ, 0 ≤ ΔX ∧ 0 ≤ ΔY ∧ 0 ≤ E ∧
      ΔX = (∫ u in (0 : ℝ)..(1 / 2), S.w u) - (1 / 8 + S.q ^ 2 / (2 * (1 + S.d (1 / 2)))) ∧
      ΔY = (∫ u in (1 / 2 : ℝ)..1, S.w u) - (1 / 8 + S.q ^ 2 / (2 * (1 - S.d (1 / 2)))) ∧
      E = 2 * S.q ^ 2 * (S.d (1 / 2)) ^ 2 / ((1 + S.d (1 / 2)) * (1 - S.d (1 / 2))) ∧
      (1 - S.d (1 / 2)) * ΔX + (1 + S.d (1 / 2)) * ΔY + E + 2 * S.q ^ 2 ≤ S.J := by
  set m := S.d (1 / 2) with hm
  have habs := S.abs_m_le
  rw [abs_le] at habs
  have ha : 0 < 1 + m := by linarith [habs.1]
  have hc : 0 < 1 - m := by linarith [habs.2]
  obtain ⟨⟨hX, -⟩, ⟨hY, -⟩⟩ := S.areas hw hq
  have hJ := S.J_ge hw
  refine ⟨(∫ u in (0 : ℝ)..(1 / 2), S.w u) - (1 / 8 + S.q ^ 2 / (2 * (1 + m))),
    (∫ u in (1 / 2 : ℝ)..1, S.w u) - (1 / 8 + S.q ^ 2 / (2 * (1 - m))),
    2 * S.q ^ 2 * m ^ 2 / ((1 + m) * (1 - m)), by linarith, by linarith, by positivity, rfl, rfl,
    rfl, ?_⟩
  have e : 2 * S.q ^ 2 * m ^ 2 / ((1 + m) * (1 - m)) =
      (1 - m) * (S.q ^ 2 / (2 * (1 + m))) + (1 + m) * (S.q ^ 2 / (2 * (1 - m))) - S.q ^ 2 := by
    field_simp
    ring
  rw [e]
  nlinarith

/-- **Lemma 5.2**, inequality: `J(w) ≥ 2 q²`. -/
theorem two_q_sq_le_J (hw : ∀ u ∈ Icc (0 : ℝ) 1, |u - 1 / 2| ≤ S.w u) : 2 * S.q ^ 2 ≤ S.J := by
  rcases (S.q_nonneg hw).eq_or_lt with h0 | hpos
  · rw [← h0]; simpa using S.J_nonneg hw
  · obtain ⟨ΔX, ΔY, E, hX, hY, hE, -, -, -, h⟩ := S.J_slack hw hpos
    have habs := S.abs_m_le
    rw [abs_le] at habs
    nlinarith [mul_nonneg (by linarith [habs.2] : (0 : ℝ) ≤ 1 - S.d (1 / 2)) hX,
      mul_nonneg (by linarith [habs.1] : (0 : ℝ) ≤ 1 + S.d (1 / 2)) hY]

end SlopeData

end Papers.OrendayLaresRockel2026XiBeta
