import Papers.Rockel2026XiBlest.FamilyOrder
import Verification.QuadraticBandTP2

/-! # The revised manuscript's positive-parameter MTP2 assertion -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

/-- A concrete Lebesgue density for the extremal copula, obtained by standardizing
the second marginal of the increasing band law. The revision's formula in
terms of the derivative of q remains a separate identification obligation. -/
theorem extremal_standardized_density (b : ℝ) (hb : 0 ≤ b) :
    (extremalCopula b hb).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity
        (fun x => ENNReal.ofReal
          ((quadraticRawBand b hb).standardizedDensity (x 0, x 1))) := by
  rw [extremalCopula, ← quadraticRawBand_copula b hb]
  exact (quadraticRawBand b hb).copula_density

/-- Every finite nonnegative member has an actual Lebesgue MTP2 density. -/
theorem extremal_hasMTP2Density (b : ℝ) (hb : 0 ≤ b) :
    (extremalCopula b hb).HasMTP2Density := quadraticBand_hasMTP2Density b hb

/-- Positive signed parameters give the same density-certified copulas. -/
theorem signed_extremal_hasMTP2Density (b : ℝ) (hb : 0 < b) :
    (signedExtremalCopula b).HasMTP2Density := by
  rw [signedExtremal_nonneg b hb.le]
  exact extremal_hasMTP2Density b hb.le

end Papers.Rockel2026XiBlest
