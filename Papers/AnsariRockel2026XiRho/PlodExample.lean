import Verification.PermutationShuffle
import Copula.Dependence.Basic

/-! # Example 1: the middle-quarter transposition is PLOD -/

open ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- The four increasing strips have vertical order 0,2,1,3. -/
noncomputable def plodShuffle : Copula 2 :=
  PermutationShuffle.copula 3 (Equiv.swap 1 2)

theorem plodShuffle_xi : plodShuffle.chatterjeeXi = 1 :=
  PermutationShuffle.xi 3 _

theorem plodShuffle_rho : plodShuffle.spearmanRho = 13 / 16 := by
  rw [plodShuffle, PermutationShuffle.rho]
  norm_num [Fin.sum_univ_succ, Equiv.swap_apply_def]

theorem plodShuffle_cdf (u v : I) :
    plodShuffle.cdf ![u,v] =
      min (stripCut (1/4) 0 u) (stripCut (1/4) 0 v) +
      min (stripCut (1/4) (1/4) u) (stripCut (1/4) (1/2) v) +
      min (stripCut (1/4) (1/2) u) (stripCut (1/4) (1/4) v) +
      min (stripCut (1/4) (3/4) u) (stripCut (1/4) (3/4) v) := by
  rw [plodShuffle, PermutationShuffle.copula, PositiveShuffle.cdf]
  norm_num [PermutationShuffle.shuffle, PermutationShuffle.strip,
    Fin.sum_univ_succ, Equiv.swap_apply_def]
  ring

private theorem cut_cases (u : I) :
    ((u : ℝ) ≤ 1/4 ∧ stripCut (1/4) 0 u = u ∧ stripCut (1/4) (1/4) u = 0 ∧
      stripCut (1/4) (1/2) u = 0 ∧ stripCut (1/4) (3/4) u = 0) ∨
    (1/4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 1/2 ∧ stripCut (1/4) 0 u = 1/4 ∧
      stripCut (1/4) (1/4) u = u-1/4 ∧ stripCut (1/4) (1/2) u = 0 ∧ stripCut (1/4) (3/4) u = 0) ∨
    (1/2 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 3/4 ∧ stripCut (1/4) 0 u = 1/4 ∧
      stripCut (1/4) (1/4) u = 1/4 ∧ stripCut (1/4) (1/2) u = u-1/2 ∧ stripCut (1/4) (3/4) u = 0) ∨
    (3/4 ≤ (u : ℝ) ∧ stripCut (1/4) 0 u = 1/4 ∧ stripCut (1/4) (1/4) u = 1/4 ∧
      stripCut (1/4) (1/2) u = 1/4 ∧ stripCut (1/4) (3/4) u = u-3/4) := by
  have h0 := u.property.1
  have h1 := u.property.2
  by_cases h : (u : ℝ) ≤ 1/4
  · left
    refine ⟨h, ?_, ?_, ?_, ?_⟩
    · simpa using stripCut_inside h0 (by linarith : (u : ℝ) ≤ 0 + 1/4)
    all_goals apply stripCut_zero (by norm_num); linarith
  · right
    by_cases h' : (u : ℝ) ≤ 1/2
    · left
      refine ⟨by linarith, h', ?_, ?_, ?_, ?_⟩
      · apply stripCut_full; linarith
      · apply stripCut_inside <;> linarith
      all_goals apply stripCut_zero (by norm_num); linarith
    · right
      by_cases h'' : (u : ℝ) ≤ 3/4
      · left
        refine ⟨by linarith, h'', ?_, ?_, ?_, ?_⟩
        · apply stripCut_full; linarith
        · apply stripCut_full; linarith
        · apply stripCut_inside <;> linarith
        · apply stripCut_zero (by norm_num); linarith
      · right
        refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
        · apply stripCut_full; linarith
        · apply stripCut_full; linarith
        · apply stripCut_full; linarith
        · apply stripCut_inside <;> linarith

set_option maxHeartbeats 2000000 in
/-- PLOD is proved at every point, including all strip edges. -/
theorem plodShuffle_isPQD : plodShuffle.IsPQD := by
  intro u v
  rw [plodShuffle_cdf]
  have hu0 := u.property.1
  have hu1 := u.property.2
  have hv0 := v.property.1
  have hv1 := v.property.2
  have hprod₁ := mul_nonneg hu0 (sub_nonneg.mpr hv1)
  have hprod₂ := mul_nonneg hv0 (sub_nonneg.mpr hu1)
  have hprod₃ := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hv1)
  rcases cut_cases u with ⟨hu, a,b,c,d⟩ | ⟨hu,hu',a,b,c,d⟩ | ⟨hu,hu',a,b,c,d⟩ | ⟨hu,a,b,c,d⟩ <;>
    rcases cut_cases v with ⟨hv,e,f,g,h⟩ | ⟨hv,hv',e,f,g,h⟩ | ⟨hv,hv',e,f,g,h⟩ | ⟨hv,e,f,g,h⟩ <;>
    rw [a,b,c,d,e,f,g,h] <;>
    simp only [min_def] <;> split_ifs <;> nlinarith

/-- The source counterexample, with its exact values and strict failure of xi<=rho. -/
theorem plod_counterexample : plodShuffle.IsPQD ∧
    plodShuffle.chatterjeeXi = 1 ∧ plodShuffle.spearmanRho = 13/16 ∧
    plodShuffle.spearmanRho < plodShuffle.chatterjeeXi := by
  rw [plodShuffle_xi, plodShuffle_rho]
  exact ⟨plodShuffle_isPQD, rfl, rfl, by norm_num⟩

end Papers.AnsariRockel2026XiRho
