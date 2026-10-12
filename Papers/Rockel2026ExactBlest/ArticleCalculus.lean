import Papers.Rockel2026ExactBlest.ExactBlestPaperParams
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The calculus argument printed in Corollary 3.2 of arXiv:2609.27634v1.
Unlike the earlier transport proof of `nu_rho_bound`, this follows the paper. -/
namespace Papers.Rockel2026ExactBlest.ArticleProof
open Set

noncomputable def leftGap (r : ℝ) := r + 1 - (3 / 4) * (1 + r) ^ (4 / 3 : ℝ)
noncomputable def rightGap (r : ℝ) := 1 - r - (3 / 4) * (1 - r) ^ (4 / 3 : ℝ)

theorem left_derivative (r : ℝ) :
    HasDerivAt leftGap (1 - (1 + r) ^ (1 / 3 : ℝ)) r := by
  have h := ((hasDerivAt_id r).add_const 1).sub
    ((((hasDerivAt_id r).const_add 1).rpow_const (p := (4 / 3 : ℝ))
      (Or.inr (by norm_num))).const_mul (3 / 4))
  convert h using 1
  · rfl
  · norm_num; ring

theorem right_derivative (r : ℝ) :
    HasDerivAt rightGap ((1 - r) ^ (1 / 3 : ℝ) - 1) r := by
  have h := ((hasDerivAt_id r).const_sub 1).sub
    ((((hasDerivAt_id r).const_sub 1).rpow_const (p := (4 / 3 : ℝ))
      (Or.inr (by norm_num))).const_mul (3 / 4))
  convert h using 1
  · rfl
  · norm_num; ring

theorem left_derivative_positive (r : ℝ) (hr : r ∈ Ico (-1 : ℝ) 0) :
    0 < 1 - (1 + r) ^ (1 / 3 : ℝ) := by
  have := Real.rpow_lt_one (by linarith [hr.1] : 0 ≤ 1 + r)
    (by linarith [hr.2] : 1 + r < 1) (by norm_num : (0 : ℝ) < 1 / 3)
  linarith

theorem right_derivative_negative (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) :
    (1 - r) ^ (1 / 3 : ℝ) - 1 < 0 := by
  have := Real.rpow_lt_one (by linarith [hr.2] : 0 ≤ 1 - r)
    (by linarith [hr.1] : 1 - r < 1) (by norm_num : (0 : ℝ) < 1 / 3)
  linarith

theorem left_increasing : StrictMonoOn leftGap (Icc (-1 : ℝ) 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun r _ => (left_derivative r).continuousAt.continuousWithinAt)
  intro r hr
  rw [interior_Icc] at hr
  rw [(left_derivative r).deriv]
  exact left_derivative_positive r ⟨hr.1.le, hr.2⟩

theorem right_decreasing : StrictAntiOn rightGap (Icc (0 : ℝ) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun r _ => (right_derivative r).continuousAt.continuousWithinAt)
  intro r hr
  rw [interior_Icc] at hr
  rw [(right_derivative r).deriv]
  exact right_derivative_negative r ⟨hr.1, hr.2.le⟩

theorem left_formula (r : ℝ) (hr : r ≤ 0) : rhoBoundary r - r = leftGap r := by
  by_cases hz : r = 0
  · subst r; norm_num [rhoBoundary, leftGap]
  · rw [rhoBoundary, ite_eq_right (by intro h; exact hz (le_antisymm hr h))]
    dsimp [leftGap]; ring

theorem right_formula (r : ℝ) (hr : 0 ≤ r) : rhoBoundary r - r = rightGap r := by
  rw [rhoBoundary, ite_eq_left hr]
  dsimp [rightGap]; ring

theorem phi_definition (r : ℝ) :
    (r ≤ 0 → rhoBoundary r - r = leftGap r) ∧
    (0 ≤ r → rhoBoundary r - r = rightGap r) :=
  ⟨left_formula r, right_formula r⟩

theorem gap_maximum (r : ℝ) (hr : r ∈ Icc (-1 : ℝ) 1) :
    rhoBoundary r - r ≤ 1 / 4 ∧ (rhoBoundary r - r = 1 / 4 ↔ r = 0) := by
  have hl : leftGap 0 = 1 / 4 := by norm_num [leftGap]
  have hu : rightGap 0 = 1 / 4 := by norm_num [rightGap]
  rcases lt_trichotomy r 0 with hn | hz | hp
  · rw [left_formula r hn.le]
    have h := left_increasing ⟨hr.1, hn.le⟩ (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 0) hn
    rw [hl] at h
    exact ⟨h.le, iff_of_false (ne_of_lt h) (ne_of_lt hn)⟩
  · subst r; norm_num [rhoBoundary]
  · rw [right_formula r hp.le]
    have h := right_decreasing (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) ⟨hp.le, hr.2⟩ hp
    rw [hu] at h
    exact ⟨h.le, iff_of_false (ne_of_lt h) (ne_of_gt hp)⟩

end Papers.Rockel2026ExactBlest.ArticleProof
