import Papers.AnsariRockelSteinmassl2026RhoGamma.ExactRegion

/-! # The largest rho-gamma discrepancy (Proposition 2.3)

An explicit half-shift certificate has supporting multiplier one. Its
exact value bounds every copula, and reflection gives the absolute bound.
-/

open ProbabilityTheory
open Copula.RankRegion

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

noncomputable def discrepancyS : ℝ := (7 + Real.sqrt 10) / 6

theorem discrepancyS_ge_one : 1 ≤ discrepancyS := by
  dsimp [discrepancyS]
  linarith [Real.sqrt_nonneg 10]

noncomputable def discrepancyCertificate : RhoGamma.AuxiliaryCertificate :=
  .halfShift discrepancyS discrepancyS_ge_one

noncomputable def discrepancyCopula : Copula 2 := discrepancyCertificate.copula

noncomputable def maximalDiscrepancy : ℝ := (1064 + 160 * Real.sqrt 10) / 4563

private theorem discrepancy_root :
    Real.sqrt (discrepancyS ^ 2 + 2 * (3 / 8 - discrepancyS / 2)) =
      (1 + Real.sqrt 10) / 3 := by
  have he : discrepancyS ^ 2 + 2 * (3 / 8 - discrepancyS / 2) =
      ((1 + Real.sqrt 10) / 3) ^ 2 := by
    dsimp [discrepancyS]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)]
  rw [he, Real.sqrt_sq (by positivity)]

private theorem discrepancy_lengths :
    discrepancyCertificate.z = (28 - 4 * Real.sqrt 10) / 39 ∧
    (discrepancyCertificate.a : ℝ) = (11 + 4 * Real.sqrt 10) / 39 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have hz : discrepancyCertificate.z = (28 - 4 * Real.sqrt 10) / 39 := by
    change 1 / (1 + (discrepancyS +
      Real.sqrt (discrepancyS ^ 2 + 2 * (3 / 8 - discrepancyS / 2))) / 2) = _
    rw [discrepancy_root]
    dsimp [discrepancyS]
    field_simp
    nlinarith
  refine ⟨hz, ?_⟩
  have ha := discrepancyCertificate.a_add_z
  rw [hz] at ha
  linarith

theorem discrepancy_support_slope : discrepancyCertificate.t = 2 / 3 := by
  rw [discrepancyCertificate.t_eq, discrepancy_lengths.1]
  change (28 - 4 * Real.sqrt 10) / 39 * discrepancyS = _
  dsimp [discrepancyS]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)]

/-- The maximizing point is the source's d0=(14-2 sqrt(10))/39. -/
theorem discrepancy_coefficients :
    discrepancyCopula.giniGamma = -1 + 8 * ((14 - 2 * Real.sqrt 10) / 39) -
      10 * ((14 - 2 * Real.sqrt 10) / 39) ^ 2 ∧
    discrepancyCopula.spearmanRho = -1 + 12 * ((14 - 2 * Real.sqrt 10) / 39) -
      24 * ((14 - 2 * Real.sqrt 10) / 39) ^ 2 +
      13 * ((14 - 2 * Real.sqrt 10) / 39) ^ 3 := by
  have hg := discrepancyCertificate.gamma
  have hr := discrepancyCertificate.rho
  change discrepancyCopula.giniGamma = _ at hg
  change discrepancyCopula.spearmanRho = _ at hr
  have hD : discrepancyCertificate.D = RhoFootrule.halfTurn := rfl
  rw [hD, RhoFootrule.halfTurn_footrule, discrepancy_lengths.1, discrepancy_lengths.2] at hg
  rw [hD, RhoFootrule.halfTurn_rho, discrepancy_lengths.1, discrepancy_lengths.2] at hr
  constructor
  · rw [hg]; ring
  · rw [hr]; ring

theorem discrepancy_value :
    discrepancyCopula.spearmanRho - discrepancyCopula.giniGamma = maximalDiscrepancy := by
  rw [discrepancy_coefficients.1, discrepancy_coefficients.2]
  dsimp [maximalDiscrepancy]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num)
  have hs3 : Real.sqrt 10 ^ 3 = 10 * Real.sqrt 10 := by rw [pow_succ, hs]
  ring_nf
  rw [hs3]
  ring

theorem rho_sub_gamma_le (C : Copula 2) :
    C.spearmanRho - C.giniGamma ≤ maximalDiscrepancy := by
  have h := discrepancyCertificate.supporting_bound C
  rw [discrepancy_support_slope] at h
  have he : (3 / 2 : ℝ) * (2 / 3) = 1 := by norm_num
  rw [he, one_mul, one_mul] at h
  exact h.trans_eq discrepancy_value

/-- The sharp absolute discrepancy for every bivariate copula. -/
theorem abs_rho_sub_gamma_le (C : Copula 2) :
    |C.spearmanRho - C.giniGamma| ≤ maximalDiscrepancy := by
  apply abs_le.mpr
  have h := rho_sub_gamma_le (C.reflect {1})
  rw [Copula.spearmanRho_reflect_second, Copula.giniGamma_reflect_second] at h
  exact ⟨by linarith, rho_sub_gamma_le C⟩

/-- Proposition 2.3 as an attained maximum, rather than just a bound. -/
theorem maximal_discrepancy_attained :
    ∃ C : Copula 2, |C.spearmanRho - C.giniGamma| = maximalDiscrepancy ∧
      ∀ D : Copula 2, |D.spearmanRho - D.giniGamma| ≤ maximalDiscrepancy := by
  refine ⟨discrepancyCopula, ?_, abs_rho_sub_gamma_le⟩
  rw [discrepancy_value, abs_of_nonneg]
  unfold maximalDiscrepancy
  positivity

end Papers.AnsariRockelSteinmassl2026RhoGamma
