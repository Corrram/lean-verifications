import Papers.Rockel2026ExactBlest.ExactBlestBetaUniqueness

/-! Pointwise local Frechet bounds used in exact-blest-regions.tex. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval BigOperators
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

theorem cdf_increment_positive (C : Copula 2) (u v : Fin 2 → I) :
    C.cdf u - C.cdf v ≤ ∑ i, max ((u i : ℝ) - (v i : ℝ)) 0 := by
  let w : Fin 2 → I := fun i => min (u i) (v i)
  have hm : C.cdf w ≤ C.cdf v := C.monotone_cdf (fun i => min_le_right _ _)
  have hl := C.cdf_sub_le_sum_abs u w
  have he (i : Fin 2) : |(u i : ℝ) - (w i : ℝ)| = max ((u i : ℝ) - (v i : ℝ)) 0 := by
    dsimp [w]
    rcases le_total (u i) (v i) with h | h
    · have h' : (u i : ℝ) ≤ v i := h
      rw [min_eq_left h', sub_self, abs_zero, max_eq_right (sub_nonpos.mpr h')]
    · have h' : (v i : ℝ) ≤ u i := h
      rw [min_eq_right h', abs_of_nonneg (sub_nonneg.mpr h'), max_eq_left (sub_nonneg.mpr h')]
  simp_rw [he] at hl
  linarith

def localUpper (q u v : ℝ) : ℝ :=
  min (min u v) (q + max (u - 1 / 2) 0 + max (v - 1 / 2) 0)

def localLower (q u v : ℝ) : ℝ :=
  max (max 0 (u + v - 1)) (q - max (1 / 2 - u) 0 - max (1 / 2 - v) 0)

theorem cdf_le_localUpper (C : Copula 2) (u v : I) :
    C.cdf ![u, v] ≤ localUpper (C.cdf ![Copula.unitHalf, Copula.unitHalf]) u v := by
  have h := cdf_increment_positive C ![u, v] ![Copula.unitHalf, Copula.unitHalf]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change C.cdf ![u, v] - C.cdf ![Copula.unitHalf, Copula.unitHalf] ≤
    max ((u : ℝ) - 1 / 2) 0 + max ((v : ℝ) - 1 / 2) 0 at h
  exact le_min (le_min (C.cdf_le_coord _ 0) (C.cdf_le_coord _ 1)) (by linarith)

theorem localLower_le_cdf (C : Copula 2) (u v : I) :
    localLower (C.cdf ![Copula.unitHalf, Copula.unitHalf]) u v ≤ C.cdf ![u, v] := by
  have h := cdf_increment_positive C ![Copula.unitHalf, Copula.unitHalf] ![u, v]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  change C.cdf ![Copula.unitHalf, Copula.unitHalf] - C.cdf ![u, v] ≤
    max (1 / 2 - (u : ℝ)) 0 + max (1 / 2 - (v : ℝ)) 0 at h
  have hl := C.sum_sub_dim_add_one_le_cdf ![u, v]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hl
  exact max_le (max_le (C.cdf_nonneg _) (by norm_num at hl; linarith)) (by linarith)

theorem local_frechet_bounds (C : Copula 2) (q : ℝ)
    (hq : C.cdf ![Copula.unitHalf, Copula.unitHalf] = q) (u v : I) :
    localLower q u v ≤ C.cdf ![u, v] ∧ C.cdf ![u, v] ≤ localUpper q u v := by
  rw [← hq]
  exact ⟨localLower_le_cdf C u v, cdf_le_localUpper C u v⟩

#assert_standard_axioms Papers.Rockel2026ExactBlest.cdf_increment_positive
#assert_standard_axioms Papers.Rockel2026ExactBlest.cdf_le_localUpper
#assert_standard_axioms Papers.Rockel2026ExactBlest.localLower_le_cdf
#assert_standard_axioms Papers.Rockel2026ExactBlest.local_frechet_bounds

end
end Papers.Rockel2026ExactBlest
