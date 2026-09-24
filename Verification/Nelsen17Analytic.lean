import Verification.BB1Conditional

/-! Analytic core for Nelsen 17. The auxiliary parameter `a` is the negative
of the paper's parameter, so the power is `a⁻¹` on both sign branches. -/

open Set

namespace Verification

noncomputable def n17A (a : ℝ) : ℝ := (2:ℝ)^a-1
noncomputable def n17Base (a t : ℝ) : ℝ := 1+n17A a*Real.exp (-t)
noncomputable def n17Psi (a t : ℝ) : ℝ := n17Base a t ^ a⁻¹-1
noncomputable def n17PsiDeriv (a t : ℝ) : ℝ := -a⁻¹*n17A a*Real.exp (-t)*n17Base a t^(a⁻¹-1)
noncomputable def n17Second (a t : ℝ) : ℝ :=
  a⁻¹*n17A a*Real.exp (-t)*n17Base a t^(a⁻¹-2)*(1+a⁻¹*n17A a*Real.exp (-t))

theorem n17A_pos {a : ℝ} (ha : 0 < a) : 0 < n17A a :=
  sub_pos.mpr (Real.one_lt_rpow (by norm_num) ha)

theorem n17A_neg {a : ℝ} (ha : a < 0) : n17A a < 0 :=
  sub_neg.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ha)

theorem n17A_ne {a : ℝ} (ha : a ≠ 0) : n17A a ≠ 0 := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · exact (n17A_neg hn).ne
  · exact (n17A_pos hp).ne'

theorem n17_coeff_pos {a : ℝ} (ha : a ≠ 0) : 0 < a⁻¹*n17A a := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · exact mul_pos_of_neg_of_neg (inv_neg''.mpr hn) (n17A_neg hn)
  · exact mul_pos (inv_pos.mpr hp) (n17A_pos hp)

theorem n17Base_pos {a t : ℝ} (ht : 0 ≤ t) : 0 < n17Base a t := by
  have he : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  by_cases ha : 0 ≤ n17A a
  · exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg ha (Real.exp_pos _).le)
  · have hh := mul_le_mul_of_nonpos_left he (le_of_not_ge ha)
    have hp := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) a
    dsimp [n17Base, n17A] at *
    nlinarith

theorem n17Base_deriv (a t : ℝ) : HasDerivAt (n17Base a) (-n17A a*Real.exp (-t)) t := by
  convert (((hasDerivAt_id t).neg.exp).const_mul (n17A a)).const_add 1 using 1
  · rfl
  · dsimp only [Pi.neg_apply, id_eq]; ring

theorem n17Psi_deriv {a t : ℝ} (ht : 0 ≤ t) : HasDerivAt (n17Psi a) (n17PsiDeriv a t) t := by
  have hh := ((n17Base_deriv a t).rpow_const (p := a⁻¹) (Or.inl (n17Base_pos ht).ne')).sub_const 1
  convert hh using 1
  · rfl
  · dsimp [n17PsiDeriv]; ring

theorem n17Psi_deriv2 {a t : ℝ} (ht : 0 ≤ t) : HasDerivAt (n17PsiDeriv a) (n17Second a t) t := by
  have hb := n17Base_pos (a := a) ht
  have hh := ((((hasDerivAt_id t).neg.exp).const_mul (-a⁻¹*n17A a)).mul
    ((n17Base_deriv a t).rpow_const (p := a⁻¹-1) (Or.inl hb.ne')))
  have he : n17Base a t^(a⁻¹-1) = n17Base a t^(a⁻¹-2)*n17Base a t := by
    rw [show a⁻¹-1 = (a⁻¹-2)+1 by ring, Real.rpow_add_one hb.ne']
  convert hh using 1
  · rfl
  · dsimp [n17Second]
    rw [show a⁻¹-1-1 = a⁻¹-2 by ring, he]
    dsimp [n17Base]
    ring

theorem n17Psi_nonneg {a t : ℝ} (ha : a ≠ 0) (ht : 0 ≤ t) : 0 ≤ n17Psi a t := by
  apply sub_nonneg.mpr
  rcases lt_or_gt_of_ne ha with hn | hp
  · apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos (n17Base_pos ht)
      (show n17Base a t ≤ 1 from by
        have hh := mul_nonpos_of_nonpos_of_nonneg (n17A_neg hn).le (Real.exp_pos (-t)).le
        dsimp [n17Base]; linarith) (inv_nonpos.mpr hn.le)
  · exact Real.one_le_rpow
      (show 1 ≤ n17Base a t from by
        have hh := mul_nonneg (n17A_pos hp).le (Real.exp_pos (-t)).le
        dsimp [n17Base]; linarith) (inv_pos.mpr hp).le

theorem n17PsiDeriv_neg {a t : ℝ} (ha : a ≠ 0) (ht : 0 ≤ t) : n17PsiDeriv a t < 0 := by
  have hh := mul_pos (mul_pos (n17_coeff_pos ha) (Real.exp_pos (-t)))
    (Real.rpow_pos_of_pos (n17Base_pos (a := a) ht) (a⁻¹-1))
  dsimp [n17PsiDeriv]
  nlinarith only [hh]

theorem n17Second_pos {a t : ℝ} (ha : a ≠ 0) (ht : 0 ≤ t) : 0 < n17Second a t := by
  have hc := mul_pos (n17_coeff_pos ha) (Real.exp_pos (-t))
  exact mul_pos (mul_pos hc (Real.rpow_pos_of_pos (n17Base_pos ht) _)) (by linarith)

theorem n17Psi_antitone {a : ℝ} (ha : a ≠ 0) : AntitoneOn (n17Psi a) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro t ht; exact (n17Psi_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n17Psi_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n17PsiDeriv_neg ha (interior_subset ht)).le

theorem n17Psi_convex {a : ℝ} (ha : a ≠ 0) : ConvexOn ℝ (Ici 0) (n17Psi a) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t ht; exact (n17Psi_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n17Psi_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n17Psi_deriv2 (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n17Second_pos ha (interior_subset ht)).le

end Verification
