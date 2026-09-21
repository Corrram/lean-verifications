import Papers.AnsariRockelSteinmassl2026RhoGamma.SourceParameters

/-! # Equations (16)-(17): the two source branches in their original distance variables -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

open RhoFootrule.UpperSpline

/-- Equation (17), first distance moment. -/
noncomputable def sourceMean (N : ℕ) (ell delta : ℝ) : ℝ :=
  ell + N * (N + 1) * delta * |delta|

/-- Equation (17), second distance moment. -/
noncomputable def sourceSquare (N : ℕ) (ell delta : ℝ) : ℝ :=
  ell * (2 * sourceMean N ell delta - ell) + 2 / 3 * N * (N + 1) * |delta| ^ 3

/-- Equation (17), endpoint value of the auxiliary potential. -/
noncomputable def sourceOffset (N : ℕ) (ell delta : ℝ) : ℝ :=
  (ell ^ 2 - (2 * ell + delta) * ell -
    ell * (1 - 2 * N * (N + 1) * |delta|) * delta) / 2

/-- On the right branch, the source delta is the library's nonnegative v. -/
theorem right_source_data (S : RhoFootrule.RightData) :
    let ell := 1 / (2 * (S.N + 1 : ℝ))
    period S.N S.v S.w = 2 * ell + S.v ∧
      (∫ x, |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) = sourceMean S.N ell S.v ∧
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂S.copula.toMeasure) = sourceSquare S.N ell S.v ∧
      offset S.N S.v S.w = sourceOffset S.N ell S.v := by
  dsimp only
  have hn : (0 : ℝ) < S.N + 1 := by positivity
  have hel : 1 / (2 * (S.N + 1 : ℝ)) = S.w + S.N * S.v := by
    apply (div_eq_iff (by positivity : (2 * (S.N + 1 : ℝ)) ≠ 0)).mpr
    nlinarith only [S.normalized]
  rw [hel, S.integral_abs_distance, S.integral_sq_distance]
  dsimp [sourceMean, sourceSquare, sourceOffset, period, offset]
  rw [abs_of_nonneg S.v_nonneg]
  refine ⟨by ring, by ring, by ring, ?_⟩
  have he : (S.w + S.N * S.v) * (1 - 2 * S.N * (S.N + 1) * S.v) = S.w := by
    nlinarith only [S.normalized, congrArg (fun r : ℝ => r * (S.N * S.v)) S.normalized]
  rw [he]
  ring

/-- On the left branch, the source delta is minus the library's v. -/
theorem left_source_data (S : RhoFootrule.LeftData) :
    let ell := 1 / (2 * (S.N : ℝ))
    period S.N S.v S.w = 2 * ell - S.v ∧
      (∫ x, |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) = sourceMean S.N ell (-S.v) ∧
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂S.copula.toMeasure) = sourceSquare S.N ell (-S.v) ∧
      offset S.N S.v S.w + S.v * S.w = sourceOffset S.N ell (-S.v) := by
  dsimp only
  have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
  have hel : 1 / (2 * (S.N : ℝ)) = S.w + (S.N + 1) * S.v := by
    apply (div_eq_iff (by positivity : (2 * (S.N : ℝ)) ≠ 0)).mpr
    nlinarith only [S.normalized]
  rw [hel, S.integral_abs_distance, S.integral_sq_distance]
  dsimp [sourceMean, sourceSquare, sourceOffset, period, offset]
  rw [abs_neg, abs_of_nonneg S.v_nonneg]
  refine ⟨by ring, by ring, by ring, ?_⟩
  have he : (S.w + (S.N + 1) * S.v) * (1 - 2 * S.N * (S.N + 1) * S.v) = S.w := by
    nlinarith only [S.normalized, congrArg (fun r : ℝ => r * ((S.N + 1) * S.v)) S.normalized]
  rw [he]
  ring

/-- Construct the source's right branch at its auxiliary multiplier s. -/
noncomputable def sourceRight (N : ℕ) (hN : 0 < N) (s : ℝ)
    (hlo : 1 / (N + 1 : ℝ) ≤ s)
    (hhi : s ≤ 1 / (2 * (N : ℝ)) + 1 / (2 * (N + 1 : ℝ))) : RhoFootrule.RightData where
  N := N
  N_pos := hN
  v := s - 1 / (N + 1 : ℝ)
  w := 1 / (2 * (N + 1 : ℝ)) - N * (s - 1 / (N + 1 : ℝ))
  v_nonneg := sub_nonneg.mpr hlo
  w_nonneg := by
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have h := mul_le_mul_of_nonneg_left hhi hn.le
    have he : (N : ℝ) * (1 / (2 * (N : ℝ)) + 1 / (2 * (N + 1 : ℝ))) =
        1 / (2 * (N + 1 : ℝ)) + N / (N + 1 : ℝ) := by field_simp; ring
    rw [he] at h
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith
  normalized := by field_simp; ring

/-- Construct the source's left branch at its auxiliary multiplier s. -/
noncomputable def sourceLeft (N : ℕ) (hN : 0 < N) (s : ℝ)
    (hlo : 1 / (2 * (N : ℝ)) + 1 / (2 * (N + 1 : ℝ)) ≤ s)
    (hhi : s ≤ 1 / (N : ℝ)) : RhoFootrule.LeftData where
  N := N
  N_pos := hN
  v := 1 / (N : ℝ) - s
  w := 1 / (2 * (N : ℝ)) - (N + 1) * (1 / (N : ℝ) - s)
  v_nonneg := sub_nonneg.mpr hhi
  w_nonneg := by
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have h := mul_le_mul_of_nonneg_left hlo (show (0 : ℝ) ≤ N + 1 by positivity)
    have he : (N + 1 : ℝ) * (1 / (2 * (N : ℝ)) + 1 / (2 * (N + 1 : ℝ))) =
        (N + 1) / (N : ℝ) - 1 / (2 * (N : ℝ)) := by field_simp; ring
    rw [he] at h
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith
  normalized := by
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    field_simp
    ring

end Papers.AnsariRockelSteinmassl2026RhoGamma
