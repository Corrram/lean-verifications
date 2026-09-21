import Papers.AnsariRockel2026RhoFootrule.MeanVariance
import Verification.PermutationShuffle

/-! # Theorem 2.1: the sharp uniform-marginal correction for finite rankings

A ranking of positive size is represented by a permutation of Fin (n+1).
The associated straight shuffle preserves each point's displacement within a strip.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

namespace Papers.AnsariRockel2026RhoFootrule

/-- The source unnormalized footrule distance Dπ. -/
noncomputable def rankingDistance (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) : ℝ :=
  ∑ i : Fin (n + 1), |(π i : ℝ) - i|

/-- The source unnormalized squared distance Sπ. -/
noncomputable def rankingSquare (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) : ℝ :=
  ∑ i : Fin (n + 1), ((π i : ℝ) - i) ^ 2

/-- Exact finite-to-population normalization of the first absolute moment. -/
theorem ranking_mean (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    meanDistance (Verification.PermutationShuffle.copula n π) =
      rankingDistance n π / ((n : ℝ) + 1) ^ 2 := by
  unfold meanDistance Verification.PermutationShuffle.copula
  rw [(Verification.PermutationShuffle.shuffle n π).integral_copula (by fun_prop)]
  unfold rankingDistance
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun u : I => |(((Verification.PermutationShuffle.shuffle n π).strip i).point u 0 : ℝ) -
      ((Verification.PermutationShuffle.shuffle n π).strip i).point u 1|) =
      fun _ : I => |((i : ℝ) - π i) / (n + 1)| := by
    funext u
    congr 1
    change (i : ℝ) / (n + 1) + 1 / (n + 1) * u -
      ((π i : ℝ) / (n + 1) + 1 / (n + 1) * u) = _
    ring
  rw [he]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  change 1 / ((n : ℝ) + 1) * |((i : ℝ) - π i) / (n + 1)| = _
  rw [abs_div, abs_of_pos (by positivity : 0 < (n : ℝ) + 1), abs_sub_comm]
  field_simp

/-- Exact finite-to-population normalization of the second moment. -/
theorem ranking_second_moment (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂(Verification.PermutationShuffle.copula n π).toMeasure) =
      rankingSquare n π / ((n : ℝ) + 1) ^ 3 := by
  have h := Verification.PermutationShuffle.rho n π
  have h' := (Verification.PermutationShuffle.copula n π).spearmanRho_eq_one_sub
  change _ = 1 - 6 * rankingSquare n π / ((n : ℝ) + 1) ^ 3 at h
  simp only [div_eq_mul_inv] at h ⊢
  linarith only [h, h']

/-- Theorem 2.1: both corrected finite-ranking inequalities, with their exact scaling. -/
theorem finite_ranking_bounds (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    let m := rankingDistance n π / ((n : ℝ) + 1) ^ 2
    let q := rankingSquare n π / ((n : ℝ) + 1) ^ 3
    m ^ 2 + minimumVariance m ≤ q ∧
      q ≤ (1 - (Real.sqrt (1 - 2 * m)) ^ 3) / 3 := by
  dsimp
  let C := Verification.PermutationShuffle.copula n π
  have hm := ranking_mean n π
  have hv := sharp_variance_bounds C
  have hr := Verification.PermutationShuffle.rho n π
  rw [distanceVariance_eq] at hv
  change meanDistance C = _ at hm
  change C.spearmanRho = 1 - 6 * rankingSquare n π / ((n : ℝ) + 1) ^ 3 at hr
  rw [hm, hr] at hv
  dsimp [maximumVariance] at hv
  simp only [div_eq_mul_inv] at hv ⊢
  constructor <;> linarith [hv.1, hv.2]

/-- Remark 2.2: the unnormalized strengthening of Cauchy--Schwarz. -/
theorem finite_ranking_cauchy_correction (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (rankingDistance n π) ^ 2 / ((n : ℝ) + 1) + ((n : ℝ) + 1) ^ 3 *
      minimumVariance (rankingDistance n π / ((n : ℝ) + 1) ^ 2) ≤ rankingSquare n π := by
  have h := (finite_ranking_bounds n π).1
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have h' := (mul_le_mul_iff_of_pos_right (pow_pos hn 3)).mpr h
  convert h' using 1 <;> field_simp

end Papers.AnsariRockel2026RhoFootrule
