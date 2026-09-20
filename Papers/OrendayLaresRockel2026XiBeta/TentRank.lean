import Papers.OrendayLaresRockel2026XiBeta.LeftProperties
import Verification.TwoStripRank

/-! # Proposition 3(ix): classical concordance of the signed tent family -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

theorem integral_tentDisplacement (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (∫ v : I, tentDisplacement b hb v) = b * |b| / 4 := by
  by_cases h : 0 ≤ b
  · change (∫ v : I, if 0 ≤ b then medianTent b v else -medianTent (-b) v) = _
    simp only [ite_eq_left h, abs_of_nonneg h]
    rw [integral_medianTent h hb.2]
    ring
  · change (∫ v : I, if 0 ≤ b then medianTent b v else -medianTent (-b) v) = _
    simp only [ite_eq_right h, abs_of_neg (lt_of_not_ge h)]
    rw [integral_neg, integral_medianTent (by linarith) (by linarith [hb.1])]
    ring

theorem leftBoundary_rho (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).spearmanRho = 3 / 4 * b * |b| := by
  rw [leftBoundary, rho_twoStrip, integral_tentDisplacement]
  ring

theorem leftBoundary_tau (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).kendallTau = 1 / 2 * b * |b| := by
  rw [leftBoundary, tau_twoStrip, integral_tentDisplacement]
  ring

end Papers.OrendayLaresRockel2026XiBeta
