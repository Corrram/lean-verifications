import Verification.Nelsen20Conditional

open Set

namespace Verification

theorem n20Second_pos {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) : 0 < n20Second p t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  unfold n20Second
  positivity

noncomputable def n20LogSecond (p t : ℝ) : ℝ :=
  (-p-2)*Real.log (Real.log (t+Real.exp 1))+Real.log (Real.log (t+Real.exp 1)+p+1)-2*Real.log (t+Real.exp 1)
noncomputable def n20LogSecondPrime (p t : ℝ) : ℝ :=
  (-p-2)/((t+Real.exp 1)*Real.log (t+Real.exp 1))+
    1/((t+Real.exp 1)*(Real.log (t+Real.exp 1)+p+1))-2/(t+Real.exp 1)

theorem n20LogSecond_deriv {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    HasDerivAt (n20LogSecond p) (n20LogSecondPrime p t) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hlp : Real.log (t+Real.exp 1)+p+1 ≠ 0 := by linarith
  have hd := ((hasDerivAt_id t).add_const (Real.exp 1)).log hx.ne'
  have hh := (((hd.log hl.ne').const_mul (-p-2)).add (((hd.add_const p).add_const 1).log hlp)).sub (hd.const_mul 2)
  convert hh using 1
  · rfl
  · dsimp [n20LogSecondPrime]; field_simp

theorem n20LogSecond_deriv2 {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    HasDerivAt (n20LogSecondPrime p)
      ((2+(p+2)*(Real.log (t+Real.exp 1)+1)/Real.log (t+Real.exp 1)^2-
        (Real.log (t+Real.exp 1)+p+2)/(Real.log (t+Real.exp 1)+p+1)^2)/(t+Real.exp 1)^2) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hlp : Real.log (t+Real.exp 1)+p+1 ≠ 0 := by linarith
  have hd := (hasDerivAt_id t).add_const (Real.exp 1)
  have hlog := hd.log hx.ne'
  have hh := (((hasDerivAt_const t (-p-2)).div (hd.mul hlog) (mul_ne_zero hx.ne' hl.ne')).add
    ((hasDerivAt_const t 1).div (hd.mul ((hlog.add_const p).add_const 1)) (mul_ne_zero hx.ne' hlp))).sub
    ((hasDerivAt_const t 2).div hd hx.ne')
  convert hh using 1
  · rfl
  · dsimp; field_simp; ring

theorem n20Second_logconvex {p : ℝ} (hp : 0 < p) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (n20Second p t)) := by
  have hc : ConvexOn ℝ (Ioi 0) (n20LogSecond p) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (n20LogSecond_deriv hp ht.le).continuousAt.continuousWithinAt
    · intro t ht; exact (n20LogSecond_deriv hp (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact (n20LogSecond_deriv2 hp (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) (le_of_lt (interior_subset ht))
      have hb : (Real.log (t+Real.exp 1)+p+2)/(Real.log (t+Real.exp 1)+p+1)^2 ≤ 2 := by
        apply (div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr
        nlinarith [sq_nonneg (Real.log (t+Real.exp 1)+p)]
      apply div_nonneg _ (sq_nonneg _)
      have hh : 0 ≤ (p+2)*(Real.log (t+Real.exp 1)+1)/Real.log (t+Real.exp 1)^2 := by positivity
      linarith
  apply (hc.add_const (Real.log p)).congr
  intro t ht
  have hx : 0 < t+Real.exp 1 := add_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht.le
  have hlp : Real.log (t+Real.exp 1)+p+1 ≠ 0 := by linarith
  have hpow := (Real.rpow_pos_of_pos hl (-p-2)).ne'
  simp only [Pi.add_apply, n20LogSecond, n20Second,
    Real.log_div (mul_ne_zero (mul_ne_zero hp.ne' hpow) hlp) (pow_ne_zero 2 hx.ne'),
    Real.log_mul (mul_ne_zero hp.ne' hpow) hlp, Real.log_mul hp.ne' hpow,
    Real.log_rpow hl, Real.log_pow]
  ring

end Verification
