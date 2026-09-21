import Papers.AnsariRockel2026XiRho.SharpGap
import Papers.AnsariRockel2026XiRho.RegionGeometry
import Verification.XiReflection

/-! # The exact xi = 3/10 slice and both sharp gap signs -/

open ProbabilityTheory Set Verification

namespace Papers.AnsariRockel2026XiRho

theorem abs_rho_sub_xi_le (C : Copula 2) : |C.spearmanRho| - C.chatterjeeXi ≤ 2 / 5 := by
  have hp := rho_sub_xi_le C
  have hn := rho_sub_xi_le (C.reflect {1})
  rw [Copula.spearmanRho_reflect_second, xi_reflect_second] at hn
  rcases le_total 0 C.spearmanRho with h | h
  · rwa [abs_of_nonneg h]
  · rwa [abs_of_nonpos h]

theorem abs_rho_sub_xi_eq_iff (C : Copula 2) :
    |C.spearmanRho| - C.chatterjeeXi = 2 / 5 ↔
      C = unitDiagonalBand ∨ C = unitDiagonalBand.reflect {1} := by
  constructor
  · intro h
    rcases le_total 0 C.spearmanRho with hp | hn
    · exact Or.inl ((rho_sub_xi_eq_iff C).mp (by simpa only [abs_of_nonneg hp] using h))
    · right
      have he : C.reflect {1} = unitDiagonalBand := (rho_sub_xi_eq_iff _).mp (by
        rw [Copula.spearmanRho_reflect_second, xi_reflect_second]
        simpa only [abs_of_nonpos hn] using h)
      simpa only [Copula.reflect_reflect] using congrArg (fun D : Copula 2 => D.reflect {1}) he
  · rintro (rfl | rfl)
    · rw [unitDiagonalBand_rho, unitDiagonalBand_xi]
      norm_num
    · rw [Copula.spearmanRho_reflect_second, xi_reflect_second,
        unitDiagonalBand_rho, unitDiagonalBand_xi]
      norm_num

/-- The complete horizontal slice of Theorem 1 at its maximal-gap point. -/
theorem xi_three_tenths_slice (y : ℝ) :
    (∃ C : Copula 2, C.chatterjeeXi = 3 / 10 ∧ C.spearmanRho = y) ↔
      |y| ≤ 7 / 10 := by
  constructor
  · rintro ⟨C, hx, hy⟩
    have h := abs_rho_sub_xi_le C
    rw [hx, hy] at h
    linarith
  · intro hy
    have hp : ((3 / 10, 7 / 10) : ℝ × ℝ) ∈ attainableRegion :=
      ⟨unitDiagonalBand, unitDiagonalBand_xi, unitDiagonalBand_rho⟩
    have hn : ((3 / 10, -(7 / 10)) : ℝ × ℝ) ∈ attainableRegion :=
      ⟨unitDiagonalBand.reflect {1}, by rw [xi_reflect_second, unitDiagonalBand_xi],
        by rw [Copula.spearmanRho_reflect_second, unitDiagonalBand_rho]⟩
    have hyb := abs_le.mp hy
    let a : ℝ := (10 * y + 7) / 14
    have ha : 0 ≤ a := by dsimp [a]; linarith [hyb.1]
    have hb : 0 ≤ 1 - a := by dsimp [a]; linarith [hyb.2]
    have h := attainable_region_convex hp hn ha hb (show a + (1 - a) = 1 by ring)
    change ∃ C : Copula 2,
      C.chatterjeeXi = a * (3 / 10) + (1 - a) * (3 / 10) ∧
      C.spearmanRho = a * (7 / 10) + (1 - a) * (-(7 / 10)) at h
    obtain ⟨C, hx, hr⟩ := h
    refine ⟨C, ?_, ?_⟩
    · nlinarith
    · dsimp [a] at hr
      linarith

/-- Uniqueness of the positive endpoint on this full slice. -/
theorem xi_three_tenths_rho_max_eq_iff (C : Copula 2) (hx : C.chatterjeeXi = 3 / 10) :
    C.spearmanRho = 7 / 10 ↔ C = unitDiagonalBand := by
  constructor
  · intro hr
    apply (rho_sub_xi_eq_iff C).mp
    rw [hx, hr]
    norm_num
  · rintro rfl
    exact unitDiagonalBand_rho

end Papers.AnsariRockel2026XiRho
