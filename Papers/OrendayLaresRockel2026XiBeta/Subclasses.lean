import Papers.OrendayLaresRockel2026XiBeta.Region
import Papers.OrendayLaresRockel2026XiBeta.LeftProperties
import Verification.CenteredProperties
import Verification.XiReflection
import Copula.Rank.Symmetry

/-! # Symmetric and quadrant-dependent attainable regions

The right endpoint uses a centered countermonotonic block with identity
outside. This alternative witness has every existential property required
by Proposition 6, including exchangeability and radial symmetry.
-/

open ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

noncomputable def symmetricRightBoundary (b : ℝ) (hb : b ∈ Icc (-1) 1) : Copula 2 :=
  centralW ⟨(1 - b) / 2, by constructor <;> linarith [hb.1, hb.2]⟩

theorem symmetricRightBoundary_xi (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (symmetricRightBoundary b hb).chatterjeeXi = 1 := centralW_xi _

theorem symmetricRightBoundary_beta (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (symmetricRightBoundary b hb).blomqvistBeta = b := by
  rw [symmetricRightBoundary, centralW_beta]
  dsimp
  ring

theorem symmetricRightBoundary_radiallySymmetric (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (symmetricRightBoundary b hb).IsRadiallySymmetric := centralW_radiallySymmetric _

theorem symmetricRightBoundary_exchangeable (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    (symmetricRightBoundary b hb).IsExchangeable := centralW_exchangeable _

theorem symmetricRightBoundary_pqd (b : ℝ) (hb : b ∈ Icc (-1) 1) (hpos : 0 ≤ b) :
    (symmetricRightBoundary b hb).IsPQD := by
  apply centralW_pqd
  change (1 - b) / 2 ≤ 1 / 2
  linarith

/-- All the existential conclusions of Proposition 6, with an alternative shuffle. -/
theorem symmetric_right_boundary_attained (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    ∃ C : Copula 2, C.chatterjeeXi = 1 ∧ C.blomqvistBeta = b ∧
      C.IsRadiallySymmetric ∧ C.IsExchangeable ∧ (0 ≤ b → C.IsPQD) :=
  ⟨symmetricRightBoundary b hb, symmetricRightBoundary_xi b hb,
    symmetricRightBoundary_beta b hb, symmetricRightBoundary_radiallySymmetric b hb,
    symmetricRightBoundary_exchangeable b hb, symmetricRightBoundary_pqd b hb⟩

/-- The intermediate-value construction stays in any class closed under mixtures. -/
theorem fixed_beta_intermediate_in_class (P : Copula 2 → Prop)
    (hMix : ∀ C D, P C → P D → ∀ a, P (C.mix D a))
    (C D : Copula 2) (hPC : P C) (hPD : P D) {b x : ℝ}
    (hC : C.blomqvistBeta = b) (hD : D.blomqvistBeta = b)
    (hxC : C.chatterjeeXi ≤ x) (hxD : x ≤ D.chatterjeeXi) :
    ∃ E : Copula 2, P E ∧ E.chatterjeeXi = x ∧ E.blomqvistBeta = b := by
  obtain ⟨a, ha⟩ := exists_unitInterval_eq (xi_mixture_continuous D C)
    (by simpa using hxC) (by simpa using hxD)
  exact ⟨D.mix C a, hMix D C hPD hPC a, ha, beta_mixture_fixed D C hD hC a⟩

/-- Corollary 7, including all boundary cases. -/
theorem exact_radiallySymmetric_xi_beta_region (x b : ℝ) :
    (∃ C : Copula 2, C.IsRadiallySymmetric ∧ C.chatterjeeXi = x ∧ C.blomqvistBeta = b) ↔
      x ∈ Icc 0 1 ∧ b ∈ Icc (-1) 1 ∧ |b| ^ 3 ≤ 2 * x := by
  constructor
  · rintro ⟨C, _, hxi, hbeta⟩
    exact (exact_xi_beta_region x b).mp ⟨C, hxi, hbeta⟩
  · rintro ⟨hx, hb, hbound⟩
    exact fixed_beta_intermediate_in_class Copula.IsRadiallySymmetric
      (fun _ _ hC hD a => hC.mix hD a) (leftBoundary b hb) (symmetricRightBoundary b hb)
      (leftBoundary_radiallySymmetric b hb) (symmetricRightBoundary_radiallySymmetric b hb)
      (leftBoundary_beta b hb) (symmetricRightBoundary_beta b hb)
      (by rw [leftBoundary_xi]; linarith) (by rw [symmetricRightBoundary_xi]; exact hx.2)

/-- Corollary 8: the same region is attained even with radial symmetry imposed. -/
theorem exact_pqd_radiallySymmetric_xi_beta_region (x b : ℝ) :
    (∃ C : Copula 2, (C.IsPQD ∧ C.IsRadiallySymmetric) ∧
      C.chatterjeeXi = x ∧ C.blomqvistBeta = b) ↔
      x ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ b ^ 3 ≤ 2 * x := by
  constructor
  · rintro ⟨C, ⟨hp, _⟩, rfl, rfl⟩
    have hb := hp.blomqvistBeta_nonneg
    exact ⟨C.chatterjeeXi_mem_Icc, ⟨hb, C.blomqvistBeta_mem_Icc.2⟩,
      by simpa only [abs_of_nonneg hb] using beta_cubic_le_two_xi C⟩
  · rintro ⟨hx, hb, hbound⟩
    have hb' : b ∈ Icc (-1) 1 := ⟨by linarith [hb.1], hb.2⟩
    exact fixed_beta_intermediate_in_class (fun C => C.IsPQD ∧ C.IsRadiallySymmetric)
      (fun _ _ hC hD a => ⟨hC.1.mix hD.1 a, hC.2.mix hD.2 a⟩)
      (leftBoundary b hb') (symmetricRightBoundary b hb')
      ⟨(leftBoundary_pqd_iff b hb').mpr hb.1, leftBoundary_radiallySymmetric b hb'⟩
      ⟨symmetricRightBoundary_pqd b hb' hb.1, symmetricRightBoundary_radiallySymmetric b hb'⟩
      (leftBoundary_beta b hb') (symmetricRightBoundary_beta b hb')
      (by rw [leftBoundary_xi, abs_of_nonneg hb.1]; linarith)
      (by rw [symmetricRightBoundary_xi]; exact hx.2)

theorem exact_pqd_xi_beta_region (x b : ℝ) :
    (∃ C : Copula 2, C.IsPQD ∧ C.chatterjeeXi = x ∧ C.blomqvistBeta = b) ↔
      x ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ b ^ 3 ≤ 2 * x := by
  constructor
  · rintro ⟨C, hp, rfl, rfl⟩
    have hb := hp.blomqvistBeta_nonneg
    exact ⟨C.chatterjeeXi_mem_Icc, ⟨hb, C.blomqvistBeta_mem_Icc.2⟩,
      by simpa only [abs_of_nonneg hb] using beta_cubic_le_two_xi C⟩
  · intro h
    obtain ⟨C, hC, hxi, hbeta⟩ := (exact_pqd_radiallySymmetric_xi_beta_region x b).mpr h
    exact ⟨C, hC.1, hxi, hbeta⟩

theorem pqd_reflect_second_isNQD (C : Copula 2) (hC : C.IsPQD) :
    (C.reflect {1}).IsNQD := by
  intro u v
  rw [Copula.cdf_reflect_second]
  have h := hC u (unitInterval.symm v)
  simp only [unitInterval.coe_symm_eq] at h
  nlinarith

/-- Remark 9, obtained by reflecting the positive quadrant-dependent region. -/
theorem exact_nqd_xi_beta_region (x b : ℝ) :
    (∃ C : Copula 2, C.IsNQD ∧ C.chatterjeeXi = x ∧ C.blomqvistBeta = b) ↔
      x ∈ Icc 0 1 ∧ b ∈ Icc (-1) 0 ∧ |b| ^ 3 ≤ 2 * x := by
  constructor
  · rintro ⟨C, hn, rfl, rfl⟩
    have h := hn Copula.unitHalf Copula.unitHalf
    have hb : C.blomqvistBeta ≤ 0 := by
      unfold Copula.blomqvistBeta
      change C.cdf ![Copula.unitHalf, Copula.unitHalf] ≤ (1 / 2 : ℝ) * (1 / 2) at h
      linarith
    exact ⟨C.chatterjeeXi_mem_Icc, ⟨C.blomqvistBeta_mem_Icc.1, hb⟩, beta_cubic_le_two_xi C⟩
  · rintro ⟨hx, hb, hbound⟩
    obtain ⟨C, hp, hxi, hbeta⟩ := (exact_pqd_xi_beta_region x (-b)).mpr
      ⟨hx, ⟨by linarith [hb.2], by linarith [hb.1]⟩,
        by simpa only [abs_of_nonpos hb.2] using hbound⟩
    refine ⟨C.reflect {1}, pqd_reflect_second_isNQD C hp, ?_, ?_⟩
    · rw [xi_reflect_second, hxi]
    · rw [Copula.blomqvistBeta_reflect_second, hbeta, neg_neg]

/-- The comparison family in Remark 10. -/
noncomputable def stochasticUpper (b : I) : Copula 2 :=
  (Copula.comonotonic 2).mix (Copula.independence 2) b

theorem stochasticUpper_isSI (b : I) : (stochasticUpper b).IsSI :=
  Copula.isSI_comonotonic.mix Copula.isSI_independence b

theorem stochasticUpper_beta (b : I) : (stochasticUpper b).blomqvistBeta = b := by
  simp [stochasticUpper, Copula.blomqvistBeta_mix]

theorem stochasticUpper_xi (b : I) : (stochasticUpper b).chatterjeeXi = (b : ℝ) ^ 2 := by
  simp [stochasticUpper, Copula.chatterjeeXi_mix_independence]

/-- The whole inner strip from Remark 10 is attained by SI copulas. -/
theorem si_inner_region_attained (x b : ℝ) (hb : b ∈ Icc 0 1)
    (hx : b ^ 3 / 2 ≤ x ∧ x ≤ b ^ 2) :
    ∃ C : Copula 2, C.IsSI ∧ C.chatterjeeXi = x ∧ C.blomqvistBeta = b := by
  have hb' : b ∈ Icc (-1) 1 := ⟨by linarith [hb.1], hb.2⟩
  exact fixed_beta_intermediate_in_class Copula.IsSI
    (fun _ _ hC hD a => hC.mix hD a) (leftBoundary b hb') (stochasticUpper ⟨b, hb⟩)
    (leftBoundary_isSI b hb' hb.1) (stochasticUpper_isSI _)
    (leftBoundary_beta b hb') (stochasticUpper_beta _)
    (by simpa only [leftBoundary_xi, abs_of_nonneg hb.1] using hx.1)
    (by simpa only [stochasticUpper_xi] using hx.2)

/-- Reflection gives the corresponding attained strip for SD copulas. -/
theorem sd_inner_region_attained (x b : ℝ) (hb : b ∈ Icc (-1) 0)
    (hx : |b| ^ 3 / 2 ≤ x ∧ x ≤ b ^ 2) :
    ∃ C : Copula 2, C.IsSD ∧ C.chatterjeeXi = x ∧ C.blomqvistBeta = b := by
  obtain ⟨C, hs, hxi, hbeta⟩ := si_inner_region_attained x (-b)
    ⟨by linarith [hb.2], by linarith [hb.1]⟩
    ⟨by simpa only [abs_of_nonpos hb.2] using hx.1, by simpa only [neg_sq] using hx.2⟩
  refine ⟨C.reflect {1}, (Copula.isSD_reflect_second_iff C).mpr hs, ?_, ?_⟩
  · rw [xi_reflect_second, hxi]
  · rw [Copula.blomqvistBeta_reflect_second, hbeta, neg_neg]

theorem si_region_outer_bound (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi ∈ Icc 0 1 ∧ C.blomqvistBeta ∈ Icc 0 1 ∧
      C.blomqvistBeta ^ 3 ≤ 2 * C.chatterjeeXi :=
  (exact_pqd_xi_beta_region _ _).mp ⟨C, hC.isPQD, rfl, rfl⟩

theorem sd_region_outer_bound (C : Copula 2) (hC : C.IsSD) :
    C.chatterjeeXi ∈ Icc 0 1 ∧ C.blomqvistBeta ∈ Icc (-1) 0 ∧
      |C.blomqvistBeta| ^ 3 ≤ 2 * C.chatterjeeXi :=
  (exact_nqd_xi_beta_region _ _).mp ⟨C, hC.isNQD, rfl, rfl⟩

end Papers.OrendayLaresRockel2026XiBeta
