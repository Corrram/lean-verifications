import Verification.DiagonalBand

/-! # Pointwise ordering of normalized clamped-affine copulas -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- Equal means and ordered slopes imply the correct order of every lower partial integral. -/
theorem clamped_prefix_order {a b c d : ℝ} (hbd : b ≤ d)
    (hm : clampedMean b a = clampedMean d c) (u : I) :
    (∫ t in Iic u, unitClamp (a - b * (t : ℝ))) ≤
      ∫ t in Iic u, unitClamp (c - d * (t : ℝ)) := by
  have hi₁ : Integrable (fun t : I => unitClamp (a - b * (t : ℝ))) :=
    Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)
  have hi₂ : Integrable (fun t : I => unitClamp (c - d * (t : ℝ))) :=
    Copula.integrable_continuous_unit volume (by unfold unitClamp; fun_prop)
  by_cases hu : a - b * (u : ℝ) ≤ c - d * (u : ℝ)
  · apply setIntegral_mono_on hi₁.integrableOn hi₂.integrableOn measurableSet_Iic
    intro t ht
    have htu : (t : ℝ) ≤ u := ht
    have h := mul_nonneg (sub_nonneg.mpr hbd) (sub_nonneg.mpr htu)
    exact min_le_min le_rfl (max_le_max le_rfl (by nlinarith only [h, hu]))
  · have ht : (∫ t in Ioc u 1, unitClamp (c - d * (t : ℝ))) ≤
        ∫ t in Ioc u 1, unitClamp (a - b * (t : ℝ)) := by
      apply setIntegral_mono_on hi₂.integrableOn hi₁.integrableOn measurableSet_Ioc
      intro t ht
      have hut : (u : ℝ) ≤ t := ht.1.le
      have h := mul_nonneg (sub_nonneg.mpr hbd) (sub_nonneg.mpr hut)
      exact min_le_min le_rfl (max_le_max le_rfl (by nlinarith only [h, hu]))
    have h₁ := Copula.integral_Iic_add_Ioc_unit hi₁ (show u ≤ (1 : I) from u.property.2)
    have h₂ := Copula.integral_Iic_add_Ioc_unit hi₂ (show u ≤ (1 : I) from u.property.2)
    have hset : Iic (1 : I) = univ := by ext t; simp [unitInterval.le_one']
    rw [hset, Measure.restrict_univ] at h₁ h₂
    change (∫ t : I, unitClamp (a - b * (t : ℝ))) = ∫ t : I, unitClamp (c - d * (t : ℝ)) at hm
    linarith only [ht, h₁, h₂, hm]

/-- The family is increasing in the lower-orthant order, including its zero-slope endpoint. -/
theorem diagonalBand_cdf_mono {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d) (hbd : b ≤ d) (u v : I) :
    (diagonalBand b hb).cdf ![u, v] ≤ (diagonalBand d hd).cdf ![u, v] := by
  rw [diagonalBand_cdf, diagonalBand_cdf]
  exact clamped_prefix_order hbd (by rw [bandIntercept_mean, bandIntercept_mean]) u

end Verification
