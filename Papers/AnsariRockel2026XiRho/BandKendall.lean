import Papers.AnsariRockel2026XiRho.BandSymmetry
import Verification.BandTauEvaluation

/-! # Proposition 5(iii): Kendall tau for the entire source family -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

noncomputable def bandTau (b : ℝ) : ℝ :=
  if b ≤ 1 then 2*b/3-b^2/6 else 1-2/(3*b)+1/(6*b^2)

/-- An exact sampling representation, proved to equal the original source copula law. -/
theorem sourceBand_sampling (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).toMeasure = (volume : Measure (I × I)).map (bandSample b) := by
  rw [sourceBand_eq_normalizedBand]
  exact diagonalBand_toMeasure_sample b hb.le

/-- The source Kendall formula, including its parameter junction at b=1. -/
theorem sourceBand_tau (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).kendallTau = bandTau b := by
  rw [sourceBand_eq_normalizedBand]
  exact diagonalBand_tau b hb.le

theorem normalizedBand_tau (b : ℝ) (hb : 0 ≤ b) :
    (normalizedBand b hb).kendallTau = bandTau b := diagonalBand_tau b hb

/-- Negative source parameters change the sign of Kendall's tau. -/
theorem negativeSourceBand_tau (b : ℝ) (hb : 0 < b) :
    (negativeSourceBand b hb).kendallTau = -bandTau b := by
  rw [negativeSourceBand, Copula.kendallTau_reflect_first, sourceBand_tau]

/-- The unit-slope copula attaining the global rho-xi gap has tau=1/2. -/
theorem unitDiagonalBand_tau : unitDiagonalBand.kendallTau = 1/2 := by
  rw [← normalizedBand_one, normalizedBand_tau]
  norm_num [bandTau]

/-- Proposition 5 simultaneously, for every positive source parameter. -/
theorem sourceBand_rank_triple (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).chatterjeeXi = bandXi b ∧
      (sourceBand b hb).spearmanRho = bandRho b ∧
      (sourceBand b hb).kendallTau = bandTau b :=
  ⟨sourceBand_xi b hb, sourceBand_rho b hb, sourceBand_tau b hb⟩

end Papers.AnsariRockel2026XiRho
