import Papers.OrendayLaresRockel2026XiBeta.LeftProperties
import Verification.TwoStripRank

/-! # Proposition 3(vi),(viii): reverse monotonicity and exchangeability -/

open ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

private theorem medianTent_one_eq_wedge (u : I) : medianTent 1 u = medianWedge u := by
  by_cases hu : (u : ℝ) ≤ 1 / 2
  · simp only [medianWedge, medianTent, abs_of_nonpos (by linarith : (u : ℝ) - 1 / 2 ≤ 0)]
    rw [min_eq_left (by linarith), max_eq_right (by linarith [u.property.1])]
    ring
  · simp only [medianWedge, medianTent, abs_of_nonneg (by linarith : 0 ≤ (u : ℝ) - 1 / 2)]
    rw [min_eq_right (by linarith), max_eq_right (by linarith [u.property.2])]
    ring

theorem leftBoundary_one_exchangeable (hb : (1 : ℝ) ∈ Icc (-1) 1) :
    (leftBoundary 1 hb).IsExchangeable := by
  apply (Copula.isExchangeable_iff _).mpr
  intro u v
  simp only [leftBoundary, cdf_twoStrip, tentDisplacement, show (0 : ℝ) ≤ 1 by norm_num,
    ite_true, medianTent_one_eq_wedge]
  ring

theorem leftBoundary_neg_one_exchangeable (hb : (-1 : ℝ) ∈ Icc (-1) 1) :
    (leftBoundary (-1) hb).IsExchangeable := by
  apply (Copula.isExchangeable_iff _).mpr
  intro u v
  simp only [leftBoundary, cdf_twoStrip, tentDisplacement, show ¬(0 : ℝ) ≤ -1 by norm_num,
    ite_false, neg_neg, medianTent_one_eq_wedge]
  ring

theorem leftBoundary_transpose_isSI_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).transpose.IsSI ↔ b = 0 ∨ b = 1 := by
  constructor
  · intro h
    have hn : 0 ≤ b := by
      simpa only [Copula.blomqvistBeta_transpose, leftBoundary_beta] using h.isPQD.blomqvistBeta_nonneg
    let a : I := ⟨(1 - b) / 2, by constructor <;> linarith [hb.2]⟩
    have ha : a ≤ Copula.unitHalf := by change (1 - b) / 2 ≤ (1 / 2 : ℝ); linarith
    have hg : tentDisplacement b hb a = 0 := by
      change (if 0 ≤ b then medianTent b ((1 - b) / 2) else _) = 0
      rw [ite_eq_left hn, medianTent, abs_of_nonpos (by linarith)]
      have he : b / 2 - -((1 - b) / 2 - 1 / 2) = 0 := by ring
      rw [he, max_self]
    have hg' : tentDisplacement b hb Copula.unitHalf = b / 2 := by
      change (if 0 ≤ b then medianTent b (1 / 2) else _) = _
      rw [ite_eq_left hn, medianTent]
      norm_num only [sub_self, abs_zero, sub_zero]
      exact max_eq_right (by linarith)
    have hc := h 0 a Copula.unitHalf Copula.unitHalf a.property.1 ha
    simp only [Copula.cdf_transpose, leftBoundary, cdf_twoStrip, hg, hg',
      StripDisplacement.zero, mul_zero, add_zero] at hc
    norm_num [a, medianWedge, Copula.unitHalf] at hc
    rcases eq_or_lt_of_le hn with h0 | hp
    · exact Or.inl h0.symm
    · right
      apply le_antisymm hb.2
      by_contra hnot
      have hlt : b < 1 := lt_of_not_ge hnot
      nlinarith [mul_pos hp (sub_pos.mpr hlt)]
  · rintro (rfl | rfl)
    · rw [leftBoundary_zero]
      exact Copula.isCI_independence.2
    · have he : (leftBoundary 1 hb).transpose = leftBoundary 1 hb := leftBoundary_one_exchangeable hb
      rw [he]
      exact leftBoundary_isSI _ _ (by norm_num)

theorem leftBoundary_transpose_isSD_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).transpose.IsSD ↔ b = 0 ∨ b = -1 := by
  rw [← Copula.isSI_reflect_second_iff, ← Copula.transpose_reflect_first,
    leftBoundary_reflect_first]
  erw [leftBoundary_transpose_isSI_iff]
  constructor <;> rintro (h | h)
  · left; linarith
  · right; linarith
  · left; linarith
  · right; linarith

theorem leftBoundary_exchangeable_iff (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (leftBoundary b hb).IsExchangeable ↔ b = -1 ∨ b = 0 ∨ b = 1 := by
  constructor
  · intro h
    have he : (leftBoundary b hb).transpose = leftBoundary b hb := h
    rcases le_total 0 b with hn | hn
    · have hs : (leftBoundary b hb).transpose.IsSI := by rw [he]; exact leftBoundary_isSI b hb hn
      exact Or.inr ((leftBoundary_transpose_isSI_iff b hb).mp hs)
    · have hs : (leftBoundary b hb).transpose.IsSD := by rw [he]; exact leftBoundary_isSD b hb hn
      rcases (leftBoundary_transpose_isSD_iff b hb).mp hs with h0 | h1
      · exact Or.inr (Or.inl h0)
      · exact Or.inl h1
  · rintro (rfl | rfl | rfl)
    · exact leftBoundary_neg_one_exchangeable hb
    · rw [leftBoundary_zero]; exact Copula.isExchangeable_independence
    · exact leftBoundary_one_exchangeable hb

end Papers.OrendayLaresRockel2026XiBeta
