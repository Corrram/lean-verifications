import Papers.Rockel2026XiFootrule.LowerSemilinearWitnesses

/-! # Remark 2.6(c): the complete lower semilinear xi--footrule region -/

open MeasureTheory ProbabilityTheory Verification Set
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- The sharp LSL lower bound holds without assuming stochastic increase. -/
theorem lowerSemilinear_xi_le_footrule (C : Copula 2) (hC : IsLowerSemilinear C) :
    C.chatterjeeXi ≤ C.spearmanFootrule := by
  obtain ⟨D⟩ := hC
  exact D.xi_le_footrule

/-- The full LSL region has the same two boundaries as the SI region. -/
theorem exact_lowerSemilinear_xi_footrule_region (x y : ℝ) :
    (∃ C : Copula 2, IsLowerSemilinear C ∧ C.chatterjeeXi = x ∧ C.spearmanFootrule = y) ↔
      x ∈ Icc 0 1 ∧ y ∈ Icc 0 1 ∧ x ≤ y ∧ y ≤ Real.sqrt x := by
  constructor
  · rintro ⟨C, hC, rfl, rfl⟩
    have h := lowerSemilinear_xi_le_footrule C hC
    exact ⟨C.chatterjeeXi_mem_Icc, ⟨C.chatterjeeXi_nonneg.trans h,
      C.spearmanFootrule_mem_Icc.2⟩, h, footrule_le_sqrt_xi C⟩
  · rintro ⟨hx, hy, hxy, hyx⟩
    let a : I := ⟨Real.sqrt (1 - y), Real.sqrt_nonneg _,
      (Real.sqrt_le_one).mpr (by linarith [hy.1])⟩
    let b : I := ⟨y, hy⟩
    have ha : 1 - (a : ℝ) ^ 2 = y := by
      dsimp [a]
      rw [Real.sq_sqrt (by linarith [hy.2])]
      ring
    have hd := diagonalBoundary_coefficients a
    rw [ha] at hd
    have hy2 : y ^ 2 ≤ x := by
      have hs := Real.sq_sqrt hx.1
      nlinarith [Real.sqrt_nonneg x]
    obtain ⟨t, ht⟩ := exists_unitInterval_eq
      (continuous_xi_mix (diagonalBoundary a) (upperBoundary b))
      (by simpa [xi_upperBoundary, b] using hy2)
      (by simpa [hd.1] using hxy)
    refine ⟨(diagonalBoundary a).mix (upperBoundary b) t,
      (diagonalBoundary_isLowerSemilinear a).mix (upperBoundary_isLowerSemilinear b) t, ht, ?_⟩
    rw [Copula.spearmanFootrule_mix, hd.2, footrule_upperBoundary]
    change (t : ℝ) * y + (1 - (t : ℝ)) * y = y
    ring

/-- Every pair is attainable in the LSL class exactly when it is attainable in the SI class. -/
theorem lowerSemilinear_region_eq_si (x y : ℝ) :
    (∃ C : Copula 2, IsLowerSemilinear C ∧ C.chatterjeeXi = x ∧ C.spearmanFootrule = y) ↔
      ∃ C : Copula 2, C.IsSI ∧ C.chatterjeeXi = x ∧ C.spearmanFootrule = y := by
  rw [exact_lowerSemilinear_xi_footrule_region, exact_si_xi_footrule_region]

end Papers.Rockel2026XiFootrule
