import Verification.Nelsen17Conditional

open Set

namespace Verification

noncomputable def n17R (a t : ℝ) : ℝ := a⁻¹*n17A a*Real.exp (-t)
noncomputable def n17LogSecond (a t : ℝ) : ℝ :=
  -t+(a⁻¹-2)*Real.log (n17Base a t)+Real.log (1+n17R a t)
noncomputable def n17LogSecondPrime (a t : ℝ) : ℝ :=
  -1-(a⁻¹-2)*n17A a*Real.exp (-t)/n17Base a t-n17R a t/(1+n17R a t)

theorem n17R_pos {a : ℝ} (ha : a ≠ 0) (t : ℝ) : 0 < n17R a t :=
  mul_pos (n17_coeff_pos ha) (Real.exp_pos _)

theorem n17R_deriv (a t : ℝ) : HasDerivAt (n17R a) (-n17R a t) t := by
  convert ((hasDerivAt_id t).neg.exp).const_mul (a⁻¹*n17A a) using 1
  · rfl
  · dsimp [n17R]; ring

theorem n17LogSecond_deriv {a t : ℝ} (ha : a ≠ 0) (ht : 0 ≤ t) :
    HasDerivAt (n17LogSecond a) (n17LogSecondPrime a t) t := by
  have hb := n17Base_pos (a := a) ht
  have hr : 0 < 1+n17R a t := by linarith [n17R_pos ha t]
  have hh := ((hasDerivAt_id t).neg.add (((n17Base_deriv a t).log hb.ne').const_mul (a⁻¹-2))).add
    (((n17R_deriv a t).const_add 1).log hr.ne')
  convert hh using 1
  · rfl
  · dsimp [n17LogSecondPrime]; ring

theorem n17LogSecond_deriv2 {a t : ℝ} (ha : a ≠ 0) (ht : 0 ≤ t) :
    HasDerivAt (n17LogSecondPrime a)
      (n17R a t*(1-a)*(2+2*n17R a t+(1-a)*(n17R a t)^2)/
        ((n17Base a t)^2*(1+n17R a t)^2)) t := by
  have hb := n17Base_pos (a := a) ht
  have hr : 0 < 1+n17R a t := by linarith [n17R_pos ha t]
  have hh := ((((((hasDerivAt_id t).neg.exp).const_mul ((a⁻¹-2)*n17A a)).div
    (n17Base_deriv a t) hb.ne').const_sub (-1))).sub
      ((n17R_deriv a t).div ((n17R_deriv a t).const_add 1) hr.ne')
  convert hh using 1
  · rfl
  · dsimp only [Pi.neg_apply, id_eq]
    field_simp
    dsimp [n17Base, n17R]
    field_simp
    ring

theorem n17Second_logconvex {a : ℝ} (ha : a ≠ 0) (ha1 : a ≤ 1) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (n17Second a t)) := by
  have hc : ConvexOn ℝ (Ioi 0) (n17LogSecond a) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (n17LogSecond_deriv ha ht.le).continuousAt.continuousWithinAt
    · intro t ht; exact (n17LogSecond_deriv ha (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact (n17LogSecond_deriv2 ha (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t _
      have hr := (n17R_pos ha t).le
      have h1 := sub_nonneg.mpr ha1
      positivity
  apply (hc.add_const (Real.log (a⁻¹*n17A a))).congr
  intro t ht
  have hb := n17Base_pos (a := a) ht.le
  have hp := (Real.rpow_pos_of_pos hb (a⁻¹-2)).ne'
  have hr : 1+n17R a t ≠ 0 := by linarith [n17R_pos ha t]
  change n17LogSecond a t+Real.log (a⁻¹*n17A a) =
    Real.log (a⁻¹*n17A a*Real.exp (-t)*n17Base a t^(a⁻¹-2)*(1+n17R a t))
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero (n17_coeff_pos ha).ne' (Real.exp_ne_zero _)) hp) hr,
    Real.log_mul (mul_ne_zero (n17_coeff_pos ha).ne' (Real.exp_ne_zero _)) hp,
    Real.log_mul (n17_coeff_pos ha).ne' (Real.exp_ne_zero _), Real.log_rpow hb, Real.log_exp]
  dsimp [n17LogSecond]
  ring

end Verification
