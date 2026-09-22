import Verification.BandTauIntegral

/-! # Exact evaluation of the band Kendall integral -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem weighted_ramp_sq (q : I) :
    (∫ t : I, (1-(t : ℝ))*ramp q t^2) = (q : ℝ)^3/3-(q : ℝ)^4/12 := by
  have he : (fun t : I => (1-(t : ℝ))*ramp q t^2) =
      fun t : I => (1-(q : ℝ))*ramp q t^2+ramp q t^3 := by
    funext t
    unfold ramp
    rcases le_total (q : ℝ) (t : ℝ) with h | h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith)]; ring
  rw [he, integral_add (by apply Copula.integrable_continuous_unit; unfold ramp; fun_prop)
    (by apply Copula.integrable_continuous_unit; unfold ramp; fun_prop), integral_const_mul,
    integral_ramp_sq]
  have h := integral_ramp_pow q 2
  norm_num at h
  rw [h]
  ring

theorem bandTauIntegral_small {b : ℝ} (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    (∫ t : I, (1-(t : ℝ))*bandTauIntegrand b t) = 1/2-b/3+b^2/12 := by
  have he : (fun t : I => (1-(t : ℝ))*bandTauIntegrand b t) =
      fun t : I => 1-(2*b+1)*(t : ℝ)+(b^2+2*b)*(t : ℝ)^2-b^2*(t : ℝ)^3 := by
    funext t
    unfold bandTauIntegrand
    rw [max_eq_right (by nlinarith [t.property.1, t.property.2])]
    ring
  rw [he, integral_sub, integral_add, integral_sub]
  · simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
      Copula.integral_unit_id, Copula.integral_unit_pow]
    ring
  all_goals apply Copula.integrable_continuous_unit; fun_prop

theorem bandTauIntegral_large {b : ℝ} (hb : 0 < b) (hb1 : 1 ≤ b) :
    (∫ t : I, (1-(t : ℝ))*bandTauIntegrand b t) = 1/(3*b)-1/(12*b^2) := by
  let q : I := ⟨1/b, by constructor; positivity; exact (div_le_one hb).mpr hb1⟩
  have hq : b*(q : ℝ) = 1 := by dsimp [q]; field_simp
  have he : (fun t : I => (1-(t : ℝ))*bandTauIntegrand b t) =
      fun t : I => b^2*((1-(t : ℝ))*ramp q t^2) := by
    funext t
    unfold bandTauIntegrand ramp
    have hid : 1-b*(t : ℝ) = b*((q : ℝ)-(t : ℝ)) := by nlinarith only [hq]
    rw [hid]
    have hmax : max 0 (b*((q : ℝ)-(t : ℝ))) = b*max 0 ((q : ℝ)-(t : ℝ)) := by
      rcases le_total (q : ℝ) (t : ℝ) with h | h
      · rw [max_eq_left (by nlinarith), max_eq_left (by linarith), mul_zero]
      · rw [max_eq_right (by nlinarith), max_eq_right (by linarith)]
    rw [hmax]
    ring
  rw [he, integral_const_mul, weighted_ramp_sq]
  dsimp [q]
  field_simp

theorem diagonalBand_tau (b : ℝ) (hb : 0 ≤ b) :
    (diagonalBand b hb).kendallTau =
      if b ≤ 1 then 2*b/3-b^2/6 else 1-2/(3*b)+1/(6*b^2) := by
  rw [diagonalBand_tau_integral]
  split_ifs with h
  · rw [bandTauIntegral_small hb h]; ring
  · rw [bandTauIntegral_large (by linarith) (by linarith)]; ring

end Verification
