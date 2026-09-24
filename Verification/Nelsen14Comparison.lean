import Verification.BB1Conditional

open Set

namespace Verification

noncomputable def powerIncrementRatio (r t : ℝ) : ℝ := ((1+t)^r-1)/t^r

theorem powerIncrementRatio_deriv {r t : ℝ} (ht : 0 < t) :
    HasDerivAt (powerIncrementRatio r)
      (r*(1+t-(1+t)^r)/(t*(1+t)*t^r)) t := by
  have hB : 0 < 1+t := by linarith
  have hh := (((hasDerivAt_id t).const_add 1).rpow_const (p := r) (Or.inl hB.ne')).sub_const 1
  have hd := (hasDerivAt_id t).rpow_const (p := r) (Or.inl ht.ne')
  convert hh.div hd (Real.rpow_pos_of_pos ht r).ne' using 1
  · rfl
  · dsimp
    rw [Real.rpow_sub_one hB.ne', Real.rpow_sub_one ht.ne']
    field_simp
    ring

theorem powerIncrementRatio_monotone {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    MonotoneOn (powerIncrementRatio r) (Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
  · intro t ht; exact (powerIncrementRatio_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (powerIncrementRatio_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := interior_subset ht
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1+t) hr1
    rw [Real.rpow_one] at hh
    exact div_nonneg (mul_nonneg hr (sub_nonneg.mpr hh)) (by positivity)

noncomputable def n14Comparison (θ η t : ℝ) : ℝ := ((1+t^θ⁻¹)^(θ/η)-1)^η

theorem n14Comparison_ratio {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : 0 < t) :
    n14Comparison θ η t/t = (powerIncrementRatio (θ/η) (t^θ⁻¹))^η := by
  have hx : 0 < t^θ⁻¹ := Real.rpow_pos_of_pos ht _
  have hB : 0 ≤ (1+t^θ⁻¹)^(θ/η)-1 :=
    sub_nonneg.mpr (Real.one_le_rpow (by linarith) (div_nonneg hθ.le hη.le))
  unfold powerIncrementRatio n14Comparison
  rw [Real.div_rpow hB (Real.rpow_pos_of_pos hx _).le,
    ← Real.rpow_mul hx.le, show θ/η*η = θ by field_simp,
    Real.rpow_inv_rpow ht.le hθ.ne']

theorem n14Comparison_ratio_monotone {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hθη : θ ≤ η) :
    MonotoneOn (fun t => n14Comparison θ η t/t) (Ioi 0) := by
  intro s hs t ht hst
  dsimp only
  rw [n14Comparison_ratio hθ hη hs, n14Comparison_ratio hθ hη ht]
  have hx : 0 < s^θ⁻¹ := Real.rpow_pos_of_pos hs _
  have hy : 0 < t^θ⁻¹ := Real.rpow_pos_of_pos ht _
  have hr : 0 ≤ θ/η := div_nonneg hθ.le hη.le
  have hr1 : θ/η ≤ 1 := (div_le_one hη).mpr hθη
  have hi := powerIncrementRatio_monotone hr hr1 hx hy
    (Real.rpow_le_rpow hs.le hst (inv_nonneg.mpr hθ.le))
  have hn : 0 ≤ powerIncrementRatio (θ/η) (s^θ⁻¹) :=
    div_nonneg (sub_nonneg.mpr (Real.one_le_rpow (by linarith) hr)) (Real.rpow_nonneg hx.le _)
  exact Real.rpow_le_rpow hn hi hη.le

theorem n14Comparison_superadd {θ η s t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hθη : θ ≤ η)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    n14Comparison θ η s+n14Comparison θ η t ≤ n14Comparison θ η (s+t) := by
  have hz : n14Comparison θ η 0 = 0 := by
    simp [n14Comparison, Real.zero_rpow (inv_ne_zero hθ.ne'), Real.zero_rpow hη.ne']
  rcases eq_or_lt_of_le hs with he | hs'
  · subst s; simp [hz]
  rcases eq_or_lt_of_le ht with he | ht'
  · subst t; simp [hz]
  have hp : 0 < s+t := add_pos hs' ht'
  have h₁ := n14Comparison_ratio_monotone hθ hη hθη hs' hp (by linarith : s ≤ s+t)
  have h₂ := n14Comparison_ratio_monotone hθ hη hθη ht' hp (by linarith : t ≤ s+t)
  have ha := (div_le_div_iff₀ hs' hp).mp h₁
  have hb := (div_le_div_iff₀ ht' hp).mp h₂
  nlinarith

end Verification
