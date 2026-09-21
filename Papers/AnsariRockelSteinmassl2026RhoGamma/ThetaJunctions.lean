import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaInputArcs

/-! # The exact integer junction coordinates in Remark 2.2 -/

open ProbabilityTheory Copula.RankRegion

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

noncomputable def junctionKappa : ℝ := (2 + Real.sqrt 3) / 4

/-- The normalized splitting root is the same kappa at every positive integer theta. -/
theorem thetaAlpha_integer (N : ℕ) (hN : 0 < N) : thetaAlpha N = junctionKappa := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hc := congrFun (thetaInput_integer N hN) 2
  change thetaOffset N = -(1 / (8 * (N : ℝ) ^ 2)) at hc
  rw [thetaAlpha, hc]
  have he : (1 : ℝ) + 2 * (N : ℝ) ^ 2 * -(1 / (8 * (N : ℝ) ^ 2)) = 3 / 4 := by field_simp; ring
  rw [he]
  norm_num [junctionKappa]
  ring

/-- Remark 2.2: both closed coordinate formulas at every integer theta=N>=1. -/
theorem theta_integer_coordinates (N : ℕ) (hN : 0 < N) :
    thetaG N = 1 - (2 * junctionKappa ^ 2 + (N : ℝ) / 2) / ((N : ℝ) + junctionKappa) ^ 2 ∧
      thetaP N = 1 - (2 * junctionKappa ^ 3 + 3 * (N : ℝ) / 8) / ((N : ℝ) + junctionKappa) ^ 3 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hm := congrFun (thetaInput_integer N hN) 0
  have hq := congrFun (thetaInput_integer N hN) 1
  change thetaMean N = 1 / (2 * (N : ℝ)) at hm
  change thetaSquare N = 1 / (4 * (N : ℝ) ^ 2) at hq
  have hd : (N : ℝ) + junctionKappa ≠ 0 := by unfold junctionKappa; positivity
  dsimp [thetaG, thetaP, thetaA, thetaZ, thetaT]
  rw [thetaAlpha_integer N hN, hm, hq]
  constructor <;> field_simp <;> ring

end Papers.AnsariRockelSteinmassl2026RhoGamma
