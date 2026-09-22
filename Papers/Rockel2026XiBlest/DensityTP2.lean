import Papers.Rockel2026XiBlest.FamilyOrder
import Verification.QuadraticBandTP2

/-! # The revised manuscript's positive-parameter MTP2 assertion -/

open ProbabilityTheory Verification

namespace Papers.Rockel2026XiBlest

/-- Every finite nonnegative member has an actual Lebesgue MTP2 density. -/
theorem extremal_hasMTP2Density (b : ℝ) (hb : 0 ≤ b) :
    (extremalCopula b hb).HasMTP2Density := quadraticBand_hasMTP2Density b hb

/-- Positive signed parameters give the same density-certified copulas. -/
theorem signed_extremal_hasMTP2Density (b : ℝ) (hb : 0 < b) :
    (signedExtremalCopula b).HasMTP2Density := by
  rw [signedExtremal_nonneg b hb.le]
  exact extremal_hasMTP2Density b hb.le

end Papers.Rockel2026XiBlest
