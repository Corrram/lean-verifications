import Papers.AnsariRockel2026XiRho.BandSymmetry
import Verification.ClampedBandOrder

/-! # Proposition 4(i): parameter ordering of the source family -/

open ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- Every pair of nonnegative parameters is ordered pointwise, including independence. -/
theorem normalizedBand_parameter_order {b d : ℝ} (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hbd : b ≤ d) (u v : I) :
    (normalizedBand b hb).cdf ![u, v] ≤ (normalizedBand d hd).cdf ![u, v] :=
  diagonalBand_cdf_mono hb hd hbd u v

/-- Proposition 4(i) for the displayed positive source parameters. -/
theorem sourceBand_parameter_order {b d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hbd : b ≤ d) (u v : I) :
    (sourceBand b hb).cdf ![u, v] ≤ (sourceBand d hd).cdf ![u, v] := by
  rw [sourceBand_eq_normalizedBand, sourceBand_eq_normalizedBand]
  exact normalizedBand_parameter_order hb.le hd.le hbd u v

/-- The source negative-parameter family has the reversed order in its positive magnitude. -/
theorem negativeSourceBand_parameter_order {b d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hbd : b ≤ d) (u v : I) :
    (negativeSourceBand d hd).cdf ![u, v] ≤ (negativeSourceBand b hb).cdf ![u, v] := by
  rw [negativeSourceBand_cdf, negativeSourceBand_cdf]
  linarith only [sourceBand_parameter_order hb hd hbd (unitInterval.symm u) v]

end Papers.AnsariRockel2026XiRho
