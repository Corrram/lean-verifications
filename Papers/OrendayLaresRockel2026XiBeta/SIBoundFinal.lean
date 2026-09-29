import Papers.OrendayLaresRockel2026XiBeta.SIBound

/-! # The final inequality of Theorem 1.2 and its equality case

For every stochastically increasing copula `C`,
`ξ(C) ≤ 1 - (3/4)(1 - β(C))²`, with equality iff `C = R_{β(C)}`.
We also record `ξ(R_b) = 1 - (3/4)(1 - b)²`, a consequence of the equality case of Lemma 5.2.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The value of `ξ` at the right-boundary copula `R_b` (Proposition 5.3 (iii), ξ part). -/
theorem xi_Rb (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).chatterjeeXi = 1 - 3 / 4 * (1 - b) ^ 2 := by
  set s := rightSection b hb with hsdef
  have hq : s.slopeData.q = (1 - b) / 2 := by
    rw [MedianSection.slopeData_q, hsdef, rightSection_gap hb (by norm_num)]
    rw [show (1 / 2 : ℝ) - 1 / 2 = 0 by ring, abs_zero]
    exact max_eq_right (by linarith [hb.2])
  have hg : ∀ u ∈ Icc (0 : ℝ) 1, s.slopeData.w u = max |u - 1 / 2| s.slopeData.q := by
    intro u hu
    rw [MedianSection.slopeData_w, hsdef, rightSection_gap hb hu.1, hq]
  have hJ := s.slopeData.J_eq_of_eq_max hg (by rw [hq]; linarith [hb.2])
    (by rw [hq]; linarith [hb.1])
  have h := s.one_sub_xi_completion
  change (s.completion).chatterjeeXi = _
  rw [hJ, hq] at h
  linarith

/-- Stochastic increasingness forces `β ∈ [0,1]`. -/
theorem si_beta_mem_Icc (C : Copula 2) (hC : C.IsSI) : C.blomqvistBeta ∈ Icc (0 : ℝ) 1 := by
  refine ⟨?_, (C.blomqvistBeta_mem_Icc).2⟩
  have h := hC.isPQD Copula.unitHalf Copula.unitHalf
  unfold Copula.blomqvistBeta
  have : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
  rw [this] at h
  linarith

/-- The two-branch bound, together with the data needed for its equality case. -/
theorem si_bound_data (C : Copula 2) (hC : C.IsSI) :
    ∃ s : MedianSection, (∀ u : I, s.A u = C.cdf ![u, Copula.unitHalf]) ∧
      s.slopeData.q = (1 - C.blomqvistBeta) / 2 ∧
      C.chatterjeeXi ≤ s.completion.chatterjeeXi ∧
      s.completion.chatterjeeXi = 1 - 3 / 2 * s.slopeData.J ∧
      2 * s.slopeData.q ^ 2 ≤ s.slopeData.J := by
  obtain ⟨s, hs⟩ := exists_medianSection_of_isSI C hC
  refine ⟨s, hs, ?_, xi_le_completion C hC s hs, ?_, ?_⟩
  · rw [MedianSection.slopeData_q, MedianSection.gap_half]
    have h := hs Copula.unitHalf
    have : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
    rw [this] at h
    unfold Copula.blomqvistBeta
    rw [h]
    ring
  · have := s.one_sub_xi_completion; linarith
  · exact s.slopeData.two_q_sq_le_J s.slopeData_abs_le

/-- **The final inequality of Theorem 1.2**: `ξ(C) ≤ 1 - (3/4)(1 - β(C))²` for SI copulas. -/
theorem xi_le_of_isSI (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi ≤ 1 - 3 / 4 * (1 - C.blomqvistBeta) ^ 2 := by
  obtain ⟨s, -, hq, h1, h2, h3⟩ := si_bound_data C hC
  rw [hq] at h3
  nlinarith

/-- **Equality case of Theorem 1.2**: equality holds iff `C = R_{β(C)}`. -/
theorem xi_eq_iff_of_isSI (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = 1 - 3 / 4 * (1 - C.blomqvistBeta) ^ 2 ↔
      C = Rb C.blomqvistBeta (si_beta_mem_Icc C hC) := by
  constructor
  · intro hE
    obtain ⟨s, hs, hq, h1, h2, h3⟩ := si_bound_data C hC
    rw [hq] at h3
    have hJ : s.slopeData.J = 2 * s.slopeData.q ^ 2 := by
      rw [hq] at *
      nlinarith
    have hxi : C.chatterjeeXi = s.completion.chatterjeeXi := by
      rw [h2, hJ, hq]; linarith
    have hCQ := eq_completion_of_xi_eq C hC s hs hxi
    have hgap := (s.slopeData.J_eq_two_q_sq_iff s.slopeData_abs_le).1 (by rw [hq] at hJ ⊢; exact hJ)
    refine hCQ.trans ?_
    show s.completion = (rightSection C.blomqvistBeta (si_beta_mem_Icc C hC)).completion
    apply MedianSection.completion_congr
    intro u hu
    have h5 := hgap u hu
    rw [MedianSection.slopeData_w, hq] at h5
    have h6 := rightSection_gap (si_beta_mem_Icc C hC) hu.1
    have h7 := MedianSection.gap_eq s u
    have h8 := MedianSection.gap_eq (rightSection C.blomqvistBeta (si_beta_mem_Icc C hC)) u
    linarith
  · intro h
    have hb := si_beta_mem_Icc C hC
    calc C.chatterjeeXi = (Rb C.blomqvistBeta hb).chatterjeeXi := congrArg _ h
      _ = _ := xi_Rb _ hb

end Papers.OrendayLaresRockel2026XiBeta
