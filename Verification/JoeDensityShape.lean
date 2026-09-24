import Verification.JoeConditional
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set

namespace Verification

noncomputable def joeSecond (p t : ℝ) : ℝ :=
  p*Real.exp (-t)*(1-Real.exp (-t))^(p-2)*(1-p*Real.exp (-t))

theorem joePsiDeriv_deriv {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (joePsiDeriv p) (joeSecond p t) t := by
  have hA : 0 < 1-Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have hE := ((hasDerivAt_id t).neg).exp
  have hP := (hE.const_sub 1).rpow_const (p := p-1) (Or.inl hA.ne')
  have hh := (hE.const_mul (-p)).mul hP
  convert hh using 1
  · rfl
  · dsimp [joeSecond]
    rw [show p-2 = (p-1)-1 by ring, Real.rpow_sub_one hA.ne' (p-1)]
    field_simp
    ring

theorem joeSecond_pos {p t : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ht : 0 < t) : 0 < joeSecond p t := by
  have hE : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)
  have hA : 0 < 1-Real.exp (-t) := by linarith
  have hB : 0 < 1-p*Real.exp (-t) := by nlinarith [Real.exp_pos (-t)]
  exact mul_pos (mul_pos (mul_pos hp (Real.exp_pos _)) (Real.rpow_pos_of_pos hA _)) hB

noncomputable def joeLogSecond (p t : ℝ) : ℝ :=
  Real.log p-t+(p-2)*Real.log (1-Real.exp (-t))+Real.log (1-p*Real.exp (-t))
noncomputable def joeLogSecondDeriv (p t : ℝ) : ℝ :=
  -1+(p-2)*(Real.exp (-t)/(1-Real.exp (-t)))+p*Real.exp (-t)/(1-p*Real.exp (-t))

theorem joe_scaledLog_deriv {p t : ℝ} (hB : 1-p*Real.exp (-t) ≠ 0) :
    HasDerivAt (fun x => Real.log (1-p*Real.exp (-x))) (p*Real.exp (-t)/(1-p*Real.exp (-t))) t := by
  have hh := (((((hasDerivAt_id t).neg).exp).const_mul p).const_sub 1).log hB
  convert hh using 1
  · rfl
  · dsimp; ring

theorem joe_scaledLog_deriv2 {p t : ℝ} (hB : 1-p*Real.exp (-t) ≠ 0) :
    HasDerivAt (fun x => p*Real.exp (-x)/(1-p*Real.exp (-x)))
      (-p*Real.exp (-t)/(1-p*Real.exp (-t))^2) t := by
  have hE := (((hasDerivAt_id t).neg).exp).const_mul p
  convert hE.div (hE.const_sub 1) hB using 1
  · rfl
  · dsimp; ring

theorem joeLogSecond_deriv {p t : ℝ} (ht : 0 < t) (hB : 1-p*Real.exp (-t) ≠ 0) :
    HasDerivAt (joeLogSecond p) (joeLogSecondDeriv p t) t := by
  exact (((hasDerivAt_id t).const_sub (Real.log p)).add
    ((joe_logBase_deriv ht).const_mul (p-2))).add (joe_scaledLog_deriv hB)

theorem joeLogSecond_deriv2 {p t : ℝ} (ht : 0 < t) (hB : 1-p*Real.exp (-t) ≠ 0) :
    HasDerivAt (joeLogSecondDeriv p)
      ((2-p)*Real.exp (-t)/(1-Real.exp (-t))^2-p*Real.exp (-t)/(1-p*Real.exp (-t))^2) t := by
  have hh := (((joe_logBase_deriv2 ht).const_mul (p-2)).const_add (-1)).add (joe_scaledLog_deriv2 hB)
  convert hh using 1
  · rfl
  · ring

theorem joeSecond_logconvex {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (joeSecond p t)) := by
  have hA (t : ℝ) (ht : 0 < t) : 0 < 1-Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have hB (t : ℝ) (ht : 0 < t) : 0 < 1-p*Real.exp (-t) := by
    nlinarith [hA t ht, Real.exp_pos (-t)]
  have hc : ConvexOn ℝ (Ioi 0) (joeLogSecond p) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (joeLogSecond_deriv ht (hB t ht).ne').continuousAt.continuousWithinAt
    · intro t ht
      exact (joeLogSecond_deriv (interior_subset ht) (hB t (interior_subset ht)).ne').hasDerivWithinAt
    · intro t ht
      exact (joeLogSecond_deriv2 (interior_subset ht) (hB t (interior_subset ht)).ne').hasDerivWithinAt
    · intro t ht
      have ht0 : 0 < t := interior_subset ht
      have he := Real.exp_pos (-t)
      have hab : (1-Real.exp (-t))^2 ≤ (1-p*Real.exp (-t))^2 := by
        have hle : 1-Real.exp (-t) ≤ 1-p*Real.exp (-t) := by nlinarith
        nlinarith [hA t ht0]
      have hh := div_le_div_of_nonneg_left (mul_nonneg hp.le he.le) (sq_pos_of_pos (hA t ht0)) hab
      have hn : p*Real.exp (-t)/(1-Real.exp (-t))^2 ≤ (2-p)*Real.exp (-t)/(1-Real.exp (-t))^2 :=
        div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg _)
      exact sub_nonneg.mpr (hh.trans hn)
  apply hc.congr
  intro t ht
  unfold joeLogSecond joeSecond
  dsimp only
  rw [Real.log_mul (mul_ne_zero (mul_ne_zero hp.ne' (Real.exp_ne_zero _))
      (Real.rpow_pos_of_pos (hA t ht) _).ne') (hB t ht).ne',
    Real.log_mul (mul_ne_zero hp.ne' (Real.exp_ne_zero _)) (Real.rpow_pos_of_pos (hA t ht) _).ne',
    Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_rpow (hA t ht)]
  ring

end Verification
