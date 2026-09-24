import Verification.Nelsen16Conditional

open Set

namespace Verification

noncomputable def n16Second (θ t : ℝ) : ℝ := 2*θ/(n16Rad θ t)^3

theorem n16Second_pos {θ t : ℝ} (hθ : 0 < θ) : 0 < n16Second θ t :=
  div_pos (by linarith) (pow_pos (n16Rad_pos hθ) _)

theorem n16LogRad_deriv {θ t : ℝ} (hθ : 0 < θ) :
    HasDerivAt (fun x => -Real.log (n16Rad θ x)) ((1-t-θ)/(n16Rad θ t)^2) t := by
  have hh := ((n16Rad_deriv (t := t) hθ).log (n16Rad_pos hθ).ne').neg
  convert hh using 1
  ring

theorem n16LogRad_deriv2 {θ t : ℝ} (hθ : 0 < θ) :
    HasDerivAt (fun x => (1-x-θ)/(n16Rad θ x)^2)
      (((1-t-θ)^2-4*θ)/(n16Rad θ t)^4) t := by
  have hh := (((hasDerivAt_id t).const_sub 1).sub_const θ).div
    ((n16Rad_deriv (t := t) hθ).pow 2) (pow_ne_zero _ (n16Rad_pos hθ).ne')
  convert hh using 1
  · rfl
  · dsimp
    have he := n16Rad_sq (t := t) hθ.le
    field_simp [(n16Rad_pos (t := t) hθ).ne']
    nlinarith

theorem n16_density_threshold {θ : ℝ} (hθ : 3+2*Real.sqrt 2 ≤ θ) :
    1 ≤ θ ∧ 4*θ ≤ (θ-1)^2 := by
  have hs := Real.sqrt_nonneg 2
  have he := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hh := mul_nonneg (sub_nonneg.mpr hθ) (show 0 ≤ θ-(3-2*Real.sqrt 2) by linarith)
  constructor <;> nlinarith

theorem n16Second_logconvex {θ : ℝ} (hθ : 3+2*Real.sqrt 2 ≤ θ) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (n16Second θ t)) := by
  obtain ⟨hθ1,hcrit⟩ := n16_density_threshold hθ
  have hp : 0 < θ := by linarith
  have hc : ConvexOn ℝ (Ioi 0) (fun t => -Real.log (n16Rad θ t)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t _; exact (n16LogRad_deriv hp).continuousAt.continuousWithinAt
    · intro t _; exact (n16LogRad_deriv hp).hasDerivWithinAt
    · intro t _; exact (n16LogRad_deriv2 hp).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 < t := interior_subset ht
      apply div_nonneg _ (pow_nonneg (n16Rad_pos hp).le _)
      nlinarith
  apply ((hc.smul (show (0:ℝ) ≤ 3 by norm_num)).add_const (Real.log (2*θ))).congr
  intro t _
  change 3*(-Real.log (n16Rad θ t))+Real.log (2*θ) = Real.log (n16Second θ t)
  unfold n16Second
  rw [Real.log_div (by positivity : 2*θ ≠ 0) (pow_ne_zero _ (n16Rad_pos hp).ne'), Real.log_pow]
  ring

end Verification
