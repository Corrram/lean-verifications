import Papers.OrendayLaresRockel2026XiBeta.TentRank

/-! # The signed tent `g_b` and the factor `ℓ` (Section 3, version 2)

Real-variable versions of the objects of Section 3:

* `tentG b v = sgn(b) (|b|/2 - |v - 1/2|)_+` (equation (3.1)),
* `ellFun u = min(u, 1 - u)`, `sigmaFun u = 1` for `u < 1/2` and `-1` for `u ≥ 1/2`,
* its properties stated before Proposition 3.1: Lipschitz, support, `g_b(1/2) = b/2`,
  symmetry, oddness in `b`, `∫ g_b = b|b|/4`, and the a.e. derivative `g_b'`.

They are tied to the version-1 tent displacement `tentDisplacement`.
-/

open MeasureTheory ProbabilityTheory Set Verification Filter Topology
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The sign function with `sgn 0 = 0`. -/
noncomputable def sgn (b : ℝ) : ℝ := if 0 < b then 1 else if b < 0 then -1 else 0

theorem sgn_of_pos {b : ℝ} (h : 0 < b) : sgn b = 1 := by simp [sgn, h]
theorem sgn_of_neg {b : ℝ} (h : b < 0) : sgn b = -1 := by simp [sgn, not_lt.mpr h.le, h]
theorem sgn_zero : sgn 0 = 0 := by simp [sgn]
theorem sgn_neg (b : ℝ) : sgn (-b) = -sgn b := by
  rcases lt_trichotomy b 0 with h | h | h
  · rw [sgn_of_neg h, sgn_of_pos (neg_pos.mpr h)]; norm_num
  · subst h; simp [sgn_zero]
  · rw [sgn_of_pos h, sgn_of_neg (neg_neg_of_pos h)]
theorem sgn_mul_abs (b : ℝ) : sgn b * |b| = b := by
  rcases lt_trichotomy b 0 with h | h | h
  · rw [sgn_of_neg h, abs_of_neg h]; ring
  · subst h; simp [sgn_zero]
  · rw [sgn_of_pos h, abs_of_pos h]; ring

/-- The signed tent `g_b(v) = sgn(b) (|b|/2 - |v - 1/2|)_+` on the real line. -/
noncomputable def tentG (b v : ℝ) : ℝ := sgn b * medianTent |b| v

/-- `ℓ(u) = min(u, 1 - u)`. -/
noncomputable def ellFun (u : ℝ) : ℝ := min u (1 - u)

/-- `σ(u) = 1` for `u < 1/2` and `σ(u) = -1` for `u ≥ 1/2`. -/
noncomputable def sigmaFun (u : ℝ) : ℝ := if u < 1 / 2 then 1 else -1

/-- The a.e. derivative of `g_b`: `sgn(b) (1_{(α_b, 1/2)} - 1_{(1/2, 1 - α_b)})`,
where `α_b = (1 - |b|)/2`. -/
noncomputable def tentGDeriv (b v : ℝ) : ℝ :=
  sgn b * ((if (1 - |b|) / 2 < v ∧ v < 1 / 2 then 1 else 0) -
    (if 1 / 2 < v ∧ v < (1 + |b|) / 2 then 1 else 0))

theorem tentDisplacement_eq_tentG (b : ℝ) (hb : b ∈ Icc (-1) 1) (v : I) :
    tentDisplacement b hb v = tentG b v := by
  change (if 0 ≤ b then medianTent b v else -medianTent (-b) v) = _
  unfold tentG
  rcases lt_trichotomy b 0 with h | h | h
  · rw [ite_eq_right (not_le.mpr h), abs_of_neg h, sgn_of_neg h]
    ring
  · subst h
    simp [medianTent]
  · rw [ite_eq_left h.le, abs_of_pos h, sgn_of_pos h]
    ring

theorem abs_sgn_le (b : ℝ) : |sgn b| ≤ 1 := by
  rcases lt_trichotomy b 0 with h | h | h
  · rw [sgn_of_neg h]; norm_num
  · rw [h, sgn_zero]; norm_num
  · rw [sgn_of_pos h]; norm_num

theorem tentG_lipschitz (b v w : ℝ) : |tentG b v - tentG b w| ≤ |v - w| := by
  unfold tentG
  rw [← mul_sub, abs_mul]
  calc |sgn b| * |medianTent |b| v - medianTent |b| w|
      ≤ 1 * |v - w| :=
        mul_le_mul (abs_sgn_le b) (medianTent_lipschitz _ v w) (abs_nonneg _) zero_le_one
    _ = |v - w| := one_mul _

theorem tentG_eq_zero {b v : ℝ} (h : v < (1 - |b|) / 2 ∨ (1 + |b|) / 2 < v) : tentG b v = 0 := by
  unfold tentG medianTent
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have : |b| / 2 - |v - 1 / 2| ≤ 0 := by
    rcases h with h | h
    · rw [abs_of_neg (show v - 1 / 2 < 0 by linarith)]; linarith
    · rw [abs_of_pos (show 0 < v - 1 / 2 by linarith)]; linarith
  rw [max_eq_left this, mul_zero]

theorem tentG_half (b : ℝ) : tentG b (1 / 2) = b / 2 := by
  unfold tentG medianTent
  rw [sub_self, abs_zero, sub_zero, max_eq_right (by positivity)]
  have := sgn_mul_abs b
  linarith

theorem tentG_one_sub (b v : ℝ) : tentG b (1 - v) = tentG b v := by
  unfold tentG medianTent
  have : |1 - v - 1 / 2| = |v - 1 / 2| := by
    rw [← abs_neg]; congr 1; ring
  rw [this]

theorem tentG_neg (b v : ℝ) : tentG (-b) v = -tentG b v := by
  unfold tentG
  rw [sgn_neg, abs_neg]
  ring

theorem tentG_zero (v : ℝ) : tentG 0 v = 0 := by
  simp [tentG, sgn_zero]

theorem integral_tentG (b : ℝ) (hb : b ∈ Icc (-1) 1) : (∫ v : I, tentG b v) = b * |b| / 4 := by
  rw [← integral_tentDisplacement b hb]
  congr 1
  funext v
  exact (tentDisplacement_eq_tentG b hb v).symm

theorem integral_tentG_sq (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (∫ v : I, tentG b v ^ 2) = |b| ^ 3 / 12 := by
  have h : ∀ v : I, tentG b v ^ 2 = medianTent |b| v ^ 2 := by
    intro v
    unfold tentG
    rw [mul_pow]
    rcases lt_trichotomy b 0 with h | h | h
    · rw [sgn_of_neg h]; ring
    · subst h; simp [medianTent]
    · rw [sgn_of_pos h]; ring
  simp_rw [h]
  exact integral_medianTent_sq (abs_nonneg _) (abs_le.mpr hb)

/-- The derivative of `g_b` away from the three break points `α_b`, `1/2`, `1 - α_b`. -/
theorem hasDerivAt_tentG (b : ℝ) {v : ℝ} (h1 : v ≠ (1 - |b|) / 2) (h2 : v ≠ 1 / 2)
    (h3 : v ≠ (1 + |b|) / 2) : HasDerivAt (tentG b) (tentGDeriv b v) v := by
  unfold tentGDeriv
  have hb0 : 0 ≤ |b| := abs_nonneg b
  rcases lt_or_gt_of_ne h1 with hv | hv
  · -- left of the support
    have hn : ¬ ((1 - |b|) / 2 < v ∧ v < 1 / 2) := fun h => by linarith [h.1]
    have hn' : ¬ (1 / 2 < v ∧ v < (1 + |b|) / 2) := fun h => by linarith [h.1]
    rw [ite_eq_right hn, ite_eq_right hn']
    simp only [sub_self, mul_zero]
    apply (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds (show v < (1 - |b|) / 2 from hv)] with w hw
    exact tentG_eq_zero (Or.inl hw)
  · rcases lt_or_gt_of_ne h2 with hv2 | hv2
    · have hp : (1 - |b|) / 2 < v ∧ v < 1 / 2 := ⟨hv, hv2⟩
      have hn' : ¬ (1 / 2 < v ∧ v < (1 + |b|) / 2) := fun h => by linarith [h.1]
      rw [ite_eq_left hp, ite_eq_right hn']
      have hd : HasDerivAt (fun w => sgn b * (w - (1 - |b|) / 2)) (sgn b * 1) v :=
        ((hasDerivAt_id v).sub_const _).const_mul _
      simp only [sub_zero] at hd ⊢
      apply hd.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hv hv2] with w hw
      unfold tentG medianTent
      rw [abs_of_neg (show w - 1 / 2 < 0 by linarith [hw.2]), max_eq_right (by linarith [hw.1])]
      congr 1
      ring
    · rcases lt_or_gt_of_ne h3 with hv3 | hv3
      · have hp : 1 / 2 < v ∧ v < (1 + |b|) / 2 := ⟨hv2, hv3⟩
        have hn : ¬ ((1 - |b|) / 2 < v ∧ v < 1 / 2) := fun h => by linarith [h.2]
        rw [ite_eq_right hn, ite_eq_left hp]
        have hd : HasDerivAt (fun w => sgn b * ((1 + |b|) / 2 - w))
            (sgn b * (-1)) v :=
          ((hasDerivAt_id v).const_sub _).const_mul _
        simp only [zero_sub, mul_neg, mul_one] at hd ⊢
        apply hd.congr_of_eventuallyEq
        filter_upwards [Ioo_mem_nhds hv2 hv3] with w hw
        unfold tentG medianTent
        rw [abs_of_pos (show 0 < w - 1 / 2 by linarith [hw.1]), max_eq_right (by linarith [hw.2])]
        congr 1
        ring
      · have hn : ¬ ((1 - |b|) / 2 < v ∧ v < 1 / 2) := fun h => by linarith [h.2]
        have hn' : ¬ (1 / 2 < v ∧ v < (1 + |b|) / 2) := fun h => by linarith [h.2]
        rw [ite_eq_right hn, ite_eq_right hn']
        simp only [sub_self, mul_zero]
        apply (hasDerivAt_const v (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [isOpen_Ioi.mem_nhds (show (1 + |b|) / 2 < v from hv3)] with w hw
        exact tentG_eq_zero (Or.inr hw)

theorem hasDerivAt_ellFun {u : ℝ} (h : u ≠ 1 / 2) : HasDerivAt ellFun (sigmaFun u) u := by
  rcases lt_or_gt_of_ne h with hu | hu
  · rw [sigmaFun, ite_eq_left hu]
    apply (hasDerivAt_id u).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hu] with w hw
    unfold ellFun
    exact min_eq_left (by simp only [Set.mem_Iio] at hw; linarith)
  · rw [sigmaFun, ite_eq_right (not_lt.mpr hu.le)]
    have hd : HasDerivAt (fun w : ℝ => 1 - w) (-1) u := (hasDerivAt_id u).const_sub 1
    apply hd.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hu] with w hw
    unfold ellFun
    exact min_eq_right (by simp only [Set.mem_Ioi] at hw; linarith)

end Papers.OrendayLaresRockel2026XiBeta
