import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaBoundary
import Mathlib.Topology.LocallyFinite

/-! # Continuous auxiliary data across all theta breakpoints -/

open ProbabilityTheory Copula.RankRegion Set
open scoped unitInterval Topology

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

noncomputable def sourceTriple (N : ℕ) (ell delta : ℝ) : Fin 3 → ℝ :=
  ![sourceMean N ell delta, sourceSquare N ell delta, sourceOffset N ell delta]

noncomputable def contactTriple (n : ℝ) : Fin 3 → ℝ :=
  ![1 / (2 * n), 1 / (4 * n ^ 2), -(1 / (8 * n ^ 2))]

noncomputable def inputArc (N : ℕ) (s : ℝ) : Fin 3 → ℝ :=
  if 1 / (2 * (N : ℝ)) + 1 / (2 * (N + 1 : ℝ)) ≤ s
  then sourceTriple N (1 / (2 * (N : ℝ))) (s - 1 / (N : ℝ))
  else sourceTriple N (1 / (2 * (N + 1 : ℝ))) (s - 1 / (N + 1 : ℝ))

private theorem middle_triples (N : ℕ) (hN : 0 < N) :
    let L : ℝ := 1 / (2 * (N : ℝ))
    let R : ℝ := 1 / (2 * (N + 1 : ℝ))
    sourceTriple N L (R - L) = sourceTriple N R (L - R) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlr : 1 / (2 * (N + 1 : ℝ)) ≤ 1 / (2 * (N : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  funext i
  fin_cases i <;> dsimp [sourceTriple, sourceMean, sourceSquare, sourceOffset]
  all_goals rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
  all_goals field_simp; ring

/-- The left and right source formulas agree at every internal arc junction. -/
theorem continuous_inputArc (N : ℕ) (hN : 0 < N) : Continuous (inputArc N) := by
  unfold inputArc
  apply Continuous.if_le
  · apply continuous_pi
    intro i
    fin_cases i <;> dsimp [sourceTriple, sourceMean, sourceSquare, sourceOffset] <;> fun_prop
  · apply continuous_pi
    intro i
    fin_cases i <;> dsimp [sourceTriple, sourceMean, sourceSquare, sourceOffset] <;> fun_prop
  · exact continuous_const
  · exact continuous_id
  · intro s hs
    subst s
    have h := middle_triples N hN
    dsimp only at h
    convert h using 1 <;> congr 1 <;> field_simp <;> ring

/-- The integer endpoint at the start of a theta interval. -/
theorem inputArc_at_left (N : ℕ) (hN : 0 < N) : inputArc N (1 / (N : ℝ)) = contactTriple N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlr : 1 / (2 * (N + 1 : ℝ)) ≤ 1 / (2 * (N : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have he : 1 / (2 * (N : ℝ)) + 1 / (2 * (N + 1 : ℝ)) ≤ 1 / (N : ℝ) := by
    rw [show 1 / (N : ℝ) = 2 * (1 / (2 * (N : ℝ))) by field_simp]
    linarith
  rw [inputArc, ite_eq_left he]
  funext i
  fin_cases i <;> dsimp [sourceTriple, sourceMean, sourceSquare, sourceOffset, contactTriple]
  all_goals simp only [sub_self, abs_zero, mul_zero, add_zero, sub_zero]
  all_goals field_simp; norm_num

/-- The integer endpoint at the end of a theta interval. -/
theorem inputArc_at_right (N : ℕ) (hN : 0 < N) : inputArc N (1 / (N + 1 : ℝ)) = contactTriple (N + 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hlr : 1 / (2 * (N + 1 : ℝ)) < 1 / (2 * (N : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have he : ¬1 / (2 * (N : ℝ)) + 1 / (2 * (N + 1 : ℝ)) ≤ 1 / (N + 1 : ℝ) := by
    rw [show 1 / (N + 1 : ℝ) = 2 * (1 / (2 * (N + 1 : ℝ))) by field_simp]
    linarith
  rw [inputArc, ite_eq_right he]
  funext i
  fin_cases i <;> dsimp [sourceTriple, sourceMean, sourceSquare, sourceOffset, contactTriple]
  all_goals simp only [sub_self, abs_zero, mul_zero, add_zero, sub_zero]
  all_goals field_simp; norm_num

noncomputable def thetaInput (theta : ℝ) : Fin 3 → ℝ :=
  ![thetaMean theta, thetaSquare theta, thetaOffset theta]

private theorem thetaInput_of_gt_one {theta : ℝ} (ht : 1 < theta) :
    thetaInput theta = inputArc ⌊theta⌋₊ (1 / theta) := by
  have hn : (0 : ℝ) < ⌊theta⌋₊ := by exact_mod_cast Nat.floor_pos.mpr ht.le
  dsimp [thetaInput, thetaMean, thetaSquare, thetaOffset]
  simp only [not_le.mpr ht, ite_false]
  unfold thetaDelta thetaEll inputArc
  split_ifs <;> funext i <;> fin_cases i <;> dsimp [sourceTriple]
  all_goals congr 1; field_simp

/-- The source's auxiliary data at every positive integer theta. -/
theorem thetaInput_integer (N : ℕ) (hN : 0 < N) : thetaInput (N : ℝ) = contactTriple N := by
  by_cases hN1 : N = 1
  · subst N
    norm_num [thetaInput, thetaMean, thetaSquare, thetaOffset, contactTriple]
  · have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    rw [thetaInput_of_gt_one hn, Nat.floor_natCast, inputArc_at_left N hN]

/-- On a closed theta interval, the floor-based source formulas equal one continuous arc. -/
theorem thetaInput_on_interval (N : ℕ) (hN : 0 < N) {theta : ℝ}
    (ht : theta ∈ Icc (N : ℝ) (N + 1)) : thetaInput theta = inputArc N (1 / theta) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases he : theta = N + 1
  · rw [he, ← Nat.cast_add_one, thetaInput_integer (N + 1) (by omega)]
    simpa only [Nat.cast_add_one] using (inputArc_at_right N hN).symm
  · have hfloor : ⌊theta⌋₊ = N := by
      apply (Nat.floor_eq_iff (by linarith [ht.1] : 0 ≤ theta)).mpr
      exact ⟨ht.1, lt_of_le_of_ne ht.2 he⟩
    by_cases htheta : theta = 1
    · have hN1 : N = 1 := by
        have h : (N : ℝ) = 1 := by linarith [ht.1]
        exact_mod_cast h
      subst N
      rw [htheta]
      simpa using thetaInput_integer 1 (by norm_num) |>.trans (inputArc_at_left 1 (by norm_num)).symm
    · rw [thetaInput_of_gt_one (lt_of_le_of_ne (hn.trans ht.1) (Ne.symm htheta)), hfloor]

end Papers.AnsariRockelSteinmassl2026RhoGamma
