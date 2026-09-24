import Verification.Nelsen19Conditional

open Set

namespace Verification

noncomputable def n19Second (θ t : ℝ) : ℝ :=
  θ*(Real.log (t+Real.exp θ)+2)/((t+Real.exp θ)^2*Real.log (t+Real.exp θ)^3)

theorem n19Second_pos {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) : 0 < n19Second θ t := by
  have hx : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hl := n19_log_pos hθ ht
  exact div_pos (mul_pos hθ (by linarith)) (mul_pos (sq_pos_of_pos hx) (pow_pos hl _))

noncomputable def n19LogSecond (θ t : ℝ) : ℝ :=
  Real.log (Real.log (t+Real.exp θ)+2)-2*Real.log (t+Real.exp θ)-3*Real.log (Real.log (t+Real.exp θ))
noncomputable def n19LogSecondPrime (θ t : ℝ) : ℝ :=
  1/((t+Real.exp θ)*(Real.log (t+Real.exp θ)+2))-2/(t+Real.exp θ)-3/((t+Real.exp θ)*Real.log (t+Real.exp θ))

theorem n19LogSecond_deriv {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    HasDerivAt (n19LogSecond θ) (n19LogSecondPrime θ t) t := by
  have hx : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hl := n19_log_pos hθ ht
  have hd := ((hasDerivAt_id t).add_const (Real.exp θ)).log hx.ne'
  have hh := (((hd.add_const 2).log (by linarith : Real.log (t+Real.exp θ)+2 ≠ 0)).sub
    (hd.const_mul 2)).sub ((hd.log hl.ne').const_mul 3)
  convert hh using 1
  · rfl
  · dsimp [n19LogSecondPrime]; field_simp

theorem n19LogSecond_deriv2 {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    HasDerivAt (n19LogSecondPrime θ)
      ((2-(Real.log (t+Real.exp θ)+3)/(Real.log (t+Real.exp θ)+2)^2+
        3*(Real.log (t+Real.exp θ)+1)/Real.log (t+Real.exp θ)^2)/(t+Real.exp θ)^2) t := by
  have hx : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hl := n19_log_pos hθ ht
  have hl2 : Real.log (t+Real.exp θ)+2 ≠ 0 := by linarith
  have hd := (hasDerivAt_id t).add_const (Real.exp θ)
  have hlog := hd.log hx.ne'
  have hh := (((hasDerivAt_const t 1).div (hd.mul (hlog.add_const 2)) (mul_ne_zero hx.ne' hl2)).sub
    ((hasDerivAt_const t 2).div hd hx.ne')).sub
    ((hasDerivAt_const t 3).div (hd.mul hlog) (mul_ne_zero hx.ne' hl.ne'))
  convert hh using 1
  · rfl
  · dsimp; field_simp; ring

theorem n19Second_logconvex {θ : ℝ} (hθ : 0 < θ) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (n19Second θ t)) := by
  have hc : ConvexOn ℝ (Ioi 0) (n19LogSecond θ) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (n19LogSecond_deriv hθ ht.le).continuousAt.continuousWithinAt
    · intro t ht; exact (n19LogSecond_deriv hθ (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact (n19LogSecond_deriv2 hθ (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      have hl := n19_log_pos hθ (le_of_lt (interior_subset ht))
      have hb : (Real.log (t+Real.exp θ)+3)/(Real.log (t+Real.exp θ)+2)^2 ≤ 1 := by
        apply (div_le_one (sq_pos_of_pos (by linarith))).mpr
        nlinarith [sq_nonneg (Real.log (t+Real.exp θ))]
      apply div_nonneg _ (sq_nonneg _)
      have hh : 0 ≤ 3*(Real.log (t+Real.exp θ)+1)/Real.log (t+Real.exp θ)^2 := by positivity
      linarith
  apply (hc.add_const (Real.log θ)).congr
  intro t ht
  have hx : 0 < t+Real.exp θ := add_pos ht (Real.exp_pos θ)
  have hl := n19_log_pos hθ ht.le
  have hl2 : Real.log (t+Real.exp θ)+2 ≠ 0 := by linarith
  simp only [Pi.add_apply, n19LogSecond, n19Second,
    Real.log_div (mul_ne_zero hθ.ne' hl2) (mul_ne_zero (pow_ne_zero 2 hx.ne') (pow_ne_zero 3 hl.ne')),
    Real.log_mul hθ.ne' hl2, Real.log_mul (pow_ne_zero 2 hx.ne') (pow_ne_zero 3 hl.ne'), Real.log_pow]
  ring

end Verification
