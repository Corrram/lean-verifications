import Verification.BandSampling
import Verification.RampIntegrals

/-! # A one-dimensional Kendall integral for the actual sampled band -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem integral_shift_clamp {w : ℝ} (hw : 0 ≤ w) :
    (∫ z : I, unitClamp (w+(z : ℝ))) = 1-max 0 (1-w)^2/2 := by
  let q : I := ⟨max 0 (1-w), le_max_left _ _, max_le zero_le_one (by linarith)⟩
  have he (z : I) : unitClamp (w+(z : ℝ)) = 1-ramp q z := by
    have hz := z.property.1
    dsimp [unitClamp, ramp, q]
    rw [max_eq_right (by linarith : 0 ≤ w+(z : ℝ))]
    by_cases hw1 : w ≤ 1
    · rw [max_eq_right (by linarith : 0 ≤ 1-w)]
      rcases le_total (w+(z : ℝ)) 1 with h | h
      · rw [min_eq_right h, max_eq_right (by linarith)]; ring
      · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith : 1-w ≤ 0), max_eq_left (by linarith),
        min_eq_left (by linarith)]
      ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) (Copula.integrable_continuous_unit volume (continuous_ramp q)),
    integral_ramp]
  simp [q]

private theorem prefix_reflection (f : ℝ → ℝ) (u : I) :
    (∫ t in Iic u, f ((u : ℝ)-(t : ℝ))) = ∫ t in Iic u, f (t : ℝ) := by
  rw [Copula.integral_unit_Iic (fun t => f ((u : ℝ)-t)), Copula.integral_unit_Iic f,
    intervalIntegral.integral_comp_sub_left]
  simp

noncomputable def bandTauIntegrand (b : ℝ) (t : I) : ℝ := max 0 (1-b*(t : ℝ))^2

theorem bandTauIntegrand_mem {b : ℝ} (hb : 0 ≤ b) (t : I) :
    bandTauIntegrand b t ∈ Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ max 0 (1-b*(t : ℝ)) := le_max_left _ _
  have h1 : max 0 (1-b*(t : ℝ)) ≤ 1 := max_le zero_le_one (by nlinarith [t.property.1])
  dsimp [bandTauIntegrand]
  exact ⟨sq_nonneg _, by nlinarith⟩

/-- Average the CDF over the independent noise while holding the first rank fixed. -/
theorem diagonalBand_cdf_noise_integral (b : ℝ) (hb : 0 ≤ b) (u : I) :
    (∫ z : I, (diagonalBand b hb).cdf (bandSample b (u,z))) =
      (u : ℝ)-(∫ t in Iic u, bandTauIntegrand b t)/2 := by
  simp_rw [diagonalBand_cdf_sample]
  have hi : Integrable (fun p : I × I => unitClamp (b*(u : ℝ)+(p.1 : ℝ)-b*(p.2 : ℝ)))
      ((volume : Measure I).prod (volume.restrict (Iic u))) :=
    (show Continuous (fun p : I × I => unitClamp (b*(u : ℝ)+(p.1 : ℝ)-b*(p.2 : ℝ))) by
      unfold unitClamp; fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hi]
  have he : (∫ t in Iic u, ∫ z : I, unitClamp (b*(u : ℝ)+(z : ℝ)-b*(t : ℝ))) =
      ∫ t in Iic u, 1-max 0 (1-b*((u : ℝ)-(t : ℝ)))^2/2 := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    have htu : (t : ℝ) ≤ u := ht
    have hw : 0 ≤ b*((u : ℝ)-(t : ℝ)) := mul_nonneg hb (sub_nonneg.mpr htu)
    have he (z : I) : b*(u : ℝ)+(z : ℝ)-b*(t : ℝ) = b*((u : ℝ)-(t : ℝ))+(z : ℝ) := by ring
    simp_rw [he]
    exact integral_shift_clamp hw
  rw [he, integral_sub (integrable_const _) (by
    apply Copula.integrable_continuous_unit; fun_prop), integral_div]
  have hr := prefix_reflection (fun x => max 0 (1-b*x)^2) u
  rw [hr]
  simp only [setIntegral_const, Measure.real, unitInterval.volume_Iic,
    ENNReal.toReal_ofReal u.property.1, smul_eq_mul, mul_one]
  rfl

/-- Kendall's tau reduces to a bounded, one-dimensional polynomial-ramp integral. -/
theorem diagonalBand_tau_integral (b : ℝ) (hb : 0 ≤ b) :
    (diagonalBand b hb).kendallTau =
      1-2*(∫ t : I, (1-(t : ℝ))*bandTauIntegrand b t) := by
  rw [Copula.kendallTau, diagonalBand_integral_sample b hb (diagonalBand b hb).continuous_cdf]
  simp_rw [diagonalBand_cdf_noise_integral b hb]
  have hm : Measurable (bandTauIntegrand b) := by unfold bandTauIntegrand; fun_prop
  have hi := integrable_lower_integral hm (bandTauIntegrand_mem hb)
  rw [integral_sub (Copula.integrable_continuous_unit volume continuous_subtype_val) (hi.div_const 2),
    integral_div, Copula.integral_unit_id, integral_lower_integral hm (bandTauIntegrand_mem hb)]
  ring

end Verification
