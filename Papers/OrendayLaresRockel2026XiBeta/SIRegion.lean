import Papers.OrendayLaresRockel2026XiBeta.RBranchProp53
import Papers.OrendayLaresRockel2026XiBeta.Section4V2

/-! # Theorem 1.2: the exact `ξ`–`β` region of stochastically increasing copulas

`R^{SI}_{ξ,β} = R^{SI,RS}_{ξ,β} = {(x,y) ∈ [0,1]² : y³ ≤ 2x, 3(1-y)² ≤ 4(1-x)}`, and
`R^{SD} = R^{SD,RS}` is its mirror image.  Every SI copula satisfies
`ξ(C) ≤ 1 - (3/4)(1-β(C))²`, with equality iff `C = R_{β(C)}`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The region of Theorem 1.2: `{(x,y) ∈ [0,1]² : y³ ≤ 2x, 3(1-y)² ≤ 4(1-x)}`. -/
def siRegion : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 ∧ p.2 ^ 3 ≤ 2 * p.1 ∧
    3 * (1 - p.2) ^ 2 ≤ 4 * (1 - p.1)}

theorem xiBetaRegion_classSI_subset : xiBetaRegion classSI ⊆ siRegion := by
  rintro ⟨x, y⟩ ⟨C, hC, rfl, rfl⟩
  have hb := si_beta_mem_Icc C hC
  have h1 := beta_cubic_le_two_xi C
  rw [abs_of_nonneg hb.1] at h1
  have h2 := xi_le_of_isSI C hC
  refine ⟨C.chatterjeeXi_mem_Icc, hb, h1, ?_⟩
  linarith

/-- `L_b ∈ C_SI ∩ C_RS` and `R_b ∈ C_SI ∩ C_RS`, so both attain the two boundary curves. -/
theorem siRegion_subset_xiBetaRegion_classSI_rs : siRegion ⊆ xiBetaRegion (classSI ∩ classRS) := by
  rintro ⟨x, y⟩ ⟨hx, hy, h1, h2⟩
  have hy' : y ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hy.1], hy.2⟩
  have hL : leftBoundary y hy' ∈ classSI ∩ classRS :=
    ⟨leftBoundary_isSI y hy' hy.1, leftBoundary_radiallySymmetric y hy'⟩
  have hR : Rb y hy ∈ classSI ∩ classRS := ⟨Rb_isSI hy, Rb_isRadiallySymmetric hy⟩
  obtain ⟨C, hC, hxi, hbeta⟩ := interpolation_lemma (convex_si.inter convex_rs) hL hR
    (leftBoundary_beta y hy') (Rb_beta hy) (x := x) (by
      rw [leftBoundary_xi, xi_Rb y hy, abs_of_nonneg hy.1]
      exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩))
  exact ⟨C, hC, hxi, hbeta⟩

/-- **Theorem 1.2**: `R^{SI}_{ξ,β} = R^{SI,RS}_{ξ,β} = {(x,y) ∈ [0,1]² : y³ ≤ 2x,
3(1-y)² ≤ 4(1-x)}`. -/
theorem theorem_1_2_region :
    xiBetaRegion classSI = siRegion ∧ xiBetaRegion (classSI ∩ classRS) = siRegion := by
  have hmid : xiBetaRegion (classSI ∩ classRS) ⊆ xiBetaRegion classSI :=
    xiBetaRegion_mono inter_subset_left
  have h1 := xiBetaRegion_classSI_subset
  have h2 := siRegion_subset_xiBetaRegion_classSI_rs
  exact ⟨Subset.antisymm h1 (h2.trans hmid), Subset.antisymm (hmid.trans h1) h2⟩

/-- **Theorem 1.2**: `R^{SD} = R^{SD,RS}` is the mirror image `{(x, -y) : (x,y) ∈ R^{SI}}`. -/
theorem theorem_1_2_sd :
    xiBetaRegion classSD = xiBetaRegion (classSD ∩ classRS) ∧
      xiBetaRegion classSD = (fun p : ℝ × ℝ => (p.1, -p.2)) '' siRegion ∧
      xiBetaRegion (classSD ∩ classRS) = (fun p : ℝ × ℝ => (p.1, -p.2)) '' siRegion := by
  obtain ⟨h1, h2⟩ := theorem_1_2_region
  refine ⟨xiBetaRegion_sd_eq_sd_rs (h1.trans h2.symm), ?_, ?_⟩
  · rw [xiBetaRegion_sd_eq, h1]
  · rw [xiBetaRegion_sd_rs_eq, h2]

/-- **Theorem 1.2, inequality (1.5)**: every SI copula satisfies
`ξ(C) ≤ 1 - (3/4)(1 - β(C))²`, with equality if and only if `C = R_{β(C)}`. -/
theorem theorem_1_2_inequality (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi ≤ 1 - 3 / 4 * (1 - C.blomqvistBeta) ^ 2 ∧
      (C.chatterjeeXi = 1 - 3 / 4 * (1 - C.blomqvistBeta) ^ 2 ↔
        C = Rb C.blomqvistBeta (si_beta_mem_Icc C hC)) :=
  ⟨xi_le_of_isSI C hC, xi_eq_iff_of_isSI C hC⟩

/-- Inequality (1.5) in the equivalent form `3(1 - β)² ≤ 4(1 - ξ)`. -/
theorem theorem_1_2_inequality_alt (C : Copula 2) (hC : C.IsSI) :
    3 * (1 - C.blomqvistBeta) ^ 2 ≤ 4 * (1 - C.chatterjeeXi) := by
  have := xi_le_of_isSI C hC
  linarith

/-- Inequality (1.5) as a lower bound on `β`: `β(C) ≥ 1 - 2√((1 - ξ(C))/3)`. -/
theorem theorem_1_2_beta_lower (C : Copula 2) (hC : C.IsSI) :
    1 - 2 * Real.sqrt ((1 - C.chatterjeeXi) / 3) ≤ C.blomqvistBeta :=
  (one_sub_sq_le_iff C.chatterjeeXi_mem_Icc.2 C.blomqvistBeta_mem_Icc.2).1
    (theorem_1_2_inequality_alt C hC)

end Papers.OrendayLaresRockel2026XiBeta
