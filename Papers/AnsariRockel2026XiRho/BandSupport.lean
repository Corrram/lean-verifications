import Papers.AnsariRockel2026XiRho.SourceBand
import Verification.BandSupportConvexity

/-! # Proposition 2: exact support and its convexity -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- The real-coordinate support of the actual source copula is the explicit closed band. -/
theorem sourceBand_support_set (b : ℝ) (hb : 0 < b) :
    ((sourceBand b hb).toMeasure.map (fun u i => (u i : ℝ))).support = bandSupport b := by
  rw [sourceBand_eq_normalizedBand]
  exact diagonalBand_support_set hb

/-- Membership includes the entire boundary of the support. -/
theorem sourceBand_support_iff (b : ℝ) (hb : 0 < b) (x : Fin 2 → ℝ) :
    x ∈ ((sourceBand b hb).toMeasure.map (fun u i => (u i : ℝ))).support ↔
      (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧
        bandLowerEdge b (x 0) ≤ x 1 ∧ x 1 ≤ 1-bandLowerEdge b (1-x 0) := by
  rw [sourceBand_support_set]
  rfl

/-- Convexity is proved for the topological support of the actual probability measure. -/
theorem sourceBand_support_convex (b : ℝ) (hb : 0 < b) :
    Convex ℝ ((sourceBand b hb).toMeasure.map (fun u i => (u i : ℝ))).support := by
  rw [sourceBand_support_set]
  exact bandSupport_convex hb

end Papers.AnsariRockel2026XiRho
