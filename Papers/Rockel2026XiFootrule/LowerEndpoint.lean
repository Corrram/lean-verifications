import Papers.Rockel2026XiFootrule.UpperBoundary
import Papers.OrendayLaresRockel2026XiBeta.LeftBoundary
import Copula.Rank.MedianExtrema

/-! # Theorem 3.4 and the entire bottom boundary

The checkerboard is identified by its CDF on the whole square. The universal
bound and uniqueness follow from the already checked sharp xi-beta theorem
and the equivalence between minimal footrule and beta=-1.
-/

open ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

open Papers.OrendayLaresRockel2026XiBeta

/-- The two off-diagonal median cells each have uniform density two. -/
noncomputable def antiCheckerboard : Copula 2 := leftBoundary (-1) (by norm_num)

private theorem medianTent_one (v : I) : medianTent 1 v = min (v : ℝ) (1 - v) := by
  unfold medianTent
  by_cases hv : (v : ℝ) ≤ 1 / 2
  · rw [abs_of_nonpos (by linarith), min_eq_left (by linarith),
      max_eq_right (by linarith [v.property.1])]
    ring
  · rw [abs_of_nonneg (by linarith), min_eq_right (by linarith),
      max_eq_right (by linarith [v.property.2])]
    ring

/-- Integrated density of the source's two off-diagonal squares. -/
theorem antiCheckerboard_cdf (u v : I) :
    antiCheckerboard.cdf ![u, v] =
      2 * (min (u : ℝ) (1 / 2) * max 0 ((v : ℝ) - 1 / 2) +
        max 0 ((u : ℝ) - 1 / 2) * min (v : ℝ) (1 / 2)) := by
  rw [antiCheckerboard, leftBoundary_cdf]
  norm_num only [neg_nonneg, show ¬(1 : ℝ) ≤ 0 by norm_num, ite_false, neg_neg]
  rw [medianTent_one]
  simp only [min_def, max_def]
  split_ifs <;> nlinarith

theorem antiCheckerboard_xi : antiCheckerboard.chatterjeeXi = 1 / 2 := by
  rw [antiCheckerboard, leftBoundary_xi]
  norm_num

theorem antiCheckerboard_footrule : antiCheckerboard.spearmanFootrule = -1 / 2 := by
  apply (Copula.spearmanFootrule_eq_neg_half_iff_blomqvistBeta_eq_neg_one _).mpr
  exact leftBoundary_beta _ _

theorem xi_lower_bound_at_minimal_footrule (C : Copula 2)
    (hC : C.spearmanFootrule = -1 / 2) : 1 / 2 ≤ C.chatterjeeXi := by
  have hb := (C.spearmanFootrule_eq_neg_half_iff_blomqvistBeta_eq_neg_one).mp hC
  have h := beta_cubic_le_two_xi C
  rw [hb] at h
  norm_num at h
  linarith

theorem xi_minimum_at_minimal_footrule_iff (C : Copula 2)
    (hC : C.spearmanFootrule = -1 / 2) :
    C.chatterjeeXi = 1 / 2 ↔ C = antiCheckerboard := by
  have hb := (C.spearmanFootrule_eq_neg_half_iff_blomqvistBeta_eq_neg_one).mp hC
  simpa only [abs_neg, abs_one, one_pow, antiCheckerboard] using
    xi_eq_lower_iff C (-1) (by norm_num) hb

/-- The bottom boundary is attained exactly for xi in [1/2,1]. -/
theorem exact_bottom_boundary (x : ℝ) :
    (∃ C : Copula 2, C.chatterjeeXi = x ∧ C.spearmanFootrule = -1 / 2) ↔
      x ∈ Icc (1 / 2) 1 := by
  constructor
  · rintro ⟨C, rfl, hp⟩
    exact ⟨xi_lower_bound_at_minimal_footrule C hp, C.chatterjeeXi_mem_Icc.2⟩
  · intro hx
    obtain ⟨a, ha⟩ := exists_unitInterval_eq
      (continuous_xi_mix Copula.countermonotonic antiCheckerboard)
      (by simpa only [Copula.mix_zero, antiCheckerboard_xi] using hx.1)
      (by simpa only [Copula.mix_one, Copula.chatterjeeXi_countermonotonic] using hx.2)
    refine ⟨Copula.countermonotonic.mix antiCheckerboard a, ha, ?_⟩
    rw [Copula.spearmanFootrule_mix, Copula.spearmanFootrule_countermonotonic,
      antiCheckerboard_footrule]
    ring

end Papers.Rockel2026XiFootrule
