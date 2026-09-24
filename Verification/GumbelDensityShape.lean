import Verification.GumbelConditional
import Verification.Nelsen13LogDensity

open Set

namespace Verification

noncomputable def gumbelSecond (p t : ℝ) : ℝ :=
  p*t^p/t^2*(p*t^p-p+1)*Real.exp (-t^p)

theorem gumbelPsiDeriv_deriv {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (gumbelPsiDeriv p) (gumbelSecond p t) t := by
  have hP := (hasDerivAt_id t).rpow_const (p := p-1) (Or.inl ht.ne')
  have hE := (((hasDerivAt_id t).rpow_const (p := p) (Or.inl ht.ne')).neg).exp
  have hh := (hP.const_mul (-p)).mul hE
  convert hh using 1
  · rfl
  · dsimp [gumbelSecond]
    rw [Real.rpow_sub_one ht.ne' (p-1), Real.rpow_sub_one ht.ne' p]
    field_simp
    ring

theorem gumbelSecond_pos {p t : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ht : 0 < t) :
    0 < gumbelSecond p t := by
  have hY := mul_pos hp (Real.rpow_pos_of_pos ht p)
  have hB : 0 < p*t^p-p+1 := by linarith
  exact mul_pos (mul_pos (div_pos hY (sq_pos_of_pos ht)) hB) (Real.exp_pos _)

theorem gumbelSecond_logconvex {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (gumbelSecond p t)) := by
  have hB (t : ℝ) (ht : 0 < t) : p*t^p+1-p ≠ 0 := by
    have hY := mul_pos hp (Real.rpow_pos_of_pos ht p)
    exact ne_of_gt (by linarith)
  have hc : ConvexOn ℝ (Ioi 0) (n13LogSecondCore p) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (n13LogSecondCore_deriv ht (hB t ht)).continuousAt.continuousWithinAt
    · intro t ht; exact (n13LogSecondCore_deriv (interior_subset ht) (hB t (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact (n13LogSecondCore_deriv2 (interior_subset ht) (hB t (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact n13LogSecondCore_deriv2_nonneg hp hp1 (interior_subset ht)
  apply (hc.add_const (-1)).congr
  intro t ht
  have hY := mul_pos hp (Real.rpow_pos_of_pos ht p)
  have hBp : 0 < p*t^p-p+1 := by linarith
  change n13LogSecondCore p t + (-1) = Real.log (gumbelSecond p t)
  unfold n13LogSecondCore gumbelSecond
  rw [Real.log_mul (mul_ne_zero (div_ne_zero hY.ne' (pow_ne_zero _ ht.ne')) hBp.ne') (Real.exp_ne_zero _),
    Real.log_mul (div_ne_zero hY.ne' (pow_ne_zero _ ht.ne')) hBp.ne',
    Real.log_div hY.ne' (pow_ne_zero _ ht.ne'), Real.log_mul hp.ne' (Real.rpow_pos_of_pos ht _).ne',
    Real.log_rpow ht, Real.log_pow, Real.log_exp]
  rw [show p*t^p-p+1 = p*t^p+1-p by ring]
  ring

end Verification
