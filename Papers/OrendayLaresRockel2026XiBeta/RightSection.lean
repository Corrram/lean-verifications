import Papers.OrendayLaresRockel2026XiBeta.MaximalCompletion

/-! # The right-boundary median sections `A_b` and the copulas `R_b` (equation (5.5))

For `b ∈ [0,1]` the slope `p_b` equals `1` on `[0, b/2]`, `1/2` on `(b/2, 1 - b/2]` and `0`
afterwards, so that `A_b(u) = min {u, (2u + b)/4, 1/2}`.  The two-branch copula of the source is
`R_b := Q_{A_b}`, the maximal completion of `A_b`.  Its gap function is
`w_b(u) = max {|u - 1/2|, (1 - b)/2}`.
-/

open MeasureTheory ProbabilityTheory Set intervalIntegral
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The slope of `A_b`: `1` on `[0, b/2]`, `1/2` on `(b/2, 1 - b/2]`, `0` afterwards. -/
noncomputable def rightSlope (b u : ℝ) : ℝ :=
  if u ≤ b / 2 then 1 else if u ≤ 1 - b / 2 then 1 / 2 else 0

theorem antitone_rightSlope (b : ℝ) : Antitone (rightSlope b) := by
  intro x y hxy
  unfold rightSlope
  split_ifs <;> first | (exfalso; linarith) | norm_num

theorem integral_eq_of_eq_on_Ioc {f : ℝ → ℝ} {c d k : ℝ} (hcd : c ≤ d)
    (h : ∀ t ∈ Ioc c d, f t = k) : ∫ t in c..d, f t = (d - c) * k := by
  rw [intervalIntegral.integral_congr_ae (g := fun _ => k)]
  · simp
  · exact Filter.Eventually.of_forall (fun t ht => by
      rw [uIoc_of_le hcd] at ht; exact h t ht)

/-- `∫₀ᵘ p_b = min {u, (2u + b)/4, 1/2}` for `u ≥ 0` and `b ∈ [0,1]`. -/
theorem integral_rightSlope {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {u : ℝ} (hu : 0 ≤ u) :
    ∫ t in (0 : ℝ)..u, rightSlope b t = min (min u ((2 * u + b) / 4)) (1 / 2) := by
  have hi : ∀ x y : ℝ, IntervalIntegrable (rightSlope b) volume x y :=
    fun x y => (antitone_rightSlope b).intervalIntegrable
  obtain ⟨hb0, hb1⟩ := hb
  by_cases h1 : u ≤ b / 2
  · rw [integral_eq_of_eq_on_Ioc hu (k := 1) (fun t ht => by simp [rightSlope, ht.2.trans h1])]
    rw [min_eq_left (show u ≤ (2 * u + b) / 4 by linarith), min_eq_left (show u ≤ 1 / 2 by linarith)]
    ring
  · push Not at h1
    have e1 : ∫ t in (0 : ℝ)..(b / 2), rightSlope b t = b / 2 := by
      rw [integral_eq_of_eq_on_Ioc (by linarith) (k := 1)
        (fun t ht => by simp [rightSlope, ht.2])]
      ring
    by_cases h2 : u ≤ 1 - b / 2
    · rw [← integral_add_adjacent_intervals (hi 0 (b / 2)) (hi (b / 2) u), e1,
        integral_eq_of_eq_on_Ioc h1.le (k := 1 / 2)
          (fun t ht => by
            have : ¬ t ≤ b / 2 := not_le.mpr ht.1
            simp [rightSlope, this, ht.2.trans h2])]
      rw [min_eq_right (show (2 * u + b) / 4 ≤ u by linarith),
        min_eq_left (show (2 * u + b) / 4 ≤ 1 / 2 by linarith)]
      ring
    · push Not at h2
      have e2 : ∫ t in (b / 2)..(1 - b / 2), rightSlope b t = (1 - b) / 2 := by
        rw [integral_eq_of_eq_on_Ioc (by linarith) (k := 1 / 2)
          (fun t ht => by
            have : ¬ t ≤ b / 2 := not_le.mpr ht.1
            simp [rightSlope, this, ht.2])]
        ring
      rw [← integral_add_adjacent_intervals (hi 0 (b / 2)) (hi (b / 2) u), e1,
        ← integral_add_adjacent_intervals (hi (b / 2) (1 - b / 2)) (hi (1 - b / 2) u), e2,
        integral_eq_of_eq_on_Ioc h2.le (k := 0) (fun t ht => by
          have h3 : ¬ t ≤ b / 2 := not_le.mpr (by linarith [ht.1])
          have h4 : ¬ t ≤ 1 - b / 2 := not_le.mpr ht.1
          simp [rightSlope, h3, h4])]
      rw [min_eq_right (show (2 * u + b) / 4 ≤ u by linarith),
        min_eq_right (show 1 / 2 ≤ (2 * u + b) / 4 by linarith)]
      ring

/-- The median section `A_b` of equation (5.5), as an element of `S`. -/
noncomputable def rightSection (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) : MedianSection where
  p := rightSlope b
  antitone := antitone_rightSlope b
  nonneg := by unfold rightSlope; split_ifs <;> norm_num
  le_one := by unfold rightSlope; split_ifs <;> norm_num
  integral_eq := by
    rw [integral_rightSlope hb zero_le_one]
    obtain ⟨hb0, hb1⟩ := hb
    rw [min_eq_right (show (2 * 1 + b) / 4 ≤ 1 by linarith),
      min_eq_right (show 1 / 2 ≤ (2 * 1 + b) / 4 by linarith)]

/-- **The two-branch copula `R_b`** of equation (5.5): the maximal completion of `A_b`. -/
noncomputable def Rb (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) : Copula 2 :=
  (rightSection b hb).completion

theorem rightSection_A {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {u : ℝ} (hu : 0 ≤ u) :
    (rightSection b hb).A u = min (min u ((2 * u + b) / 4)) (1 / 2) :=
  integral_rightSlope hb hu

theorem rightSection_gap {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {u : ℝ} (hu : 0 ≤ u) :
    (rightSection b hb).gap u = max |u - 1 / 2| ((1 - b) / 2) := by
  rw [MedianSection.gap_eq, rightSection_A hb hu, abs_eq_max_neg]
  obtain ⟨hb0, hb1⟩ := hb
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem Rb_isSI {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) : (Rb b hb).IsSI :=
  (rightSection b hb).completion_isSI

theorem Rb_cdf_half {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (u : I) :
    (Rb b hb).cdf ![u, Copula.unitHalf] = min (min (u : ℝ) ((2 * u + b) / 4)) (1 / 2) := by
  rw [Rb, MedianSection.cdf_completion_half, rightSection_A hb u.2.1]

theorem Rb_beta {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) : (Rb b hb).blomqvistBeta = b := by
  obtain ⟨hb0, hb1⟩ := hb
  have h := Rb_cdf_half ⟨hb0, hb1⟩ Copula.unitHalf
  unfold Copula.blomqvistBeta
  rw [h]
  change 4 * min (min (1 / 2 : ℝ) ((2 * (1 / 2) + b) / 4)) (1 / 2) - 1 = b
  simp only [min_def]
  split_ifs <;> linarith

end Papers.OrendayLaresRockel2026XiBeta
