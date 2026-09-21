import Papers.Rockel2026XiFootrule.UpperBoundary
import Verification.CenteredProperties
import Verification.XiAffineRegion

/-! # Attainment and convexity in Theorem 3.3

Centered countermonotonic blocks attain every footrule value at xi=1.
Mixtures then fill fixed-footrule intervals and prove convexity of the
whole region. This does not assume or claim closure of the region.
-/

open ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- Equation (24), with the universal coefficient ranges implicit in Copula. -/
def attainableRegion : Set (ℝ × ℝ) := xiCoefficientRegion Copula.spearmanFootrule

/-- A shuffle-of-min witness: a central W block and identity outside it. -/
noncomputable def rightBoundary (a : I) : Copula 2 := centralW a

theorem rightBoundary_coefficients (a : I) :
    (rightBoundary a).chatterjeeXi = 1 ∧
      (rightBoundary a).spearmanFootrule = 1 - 3 / 2 * (a : ℝ) ^ 2 := by
  refine ⟨centralW_xi a, ?_⟩
  rw [rightBoundary, centralW, centeredOrdinal_footrule, Copula.spearmanFootrule_countermonotonic]
  ring

/-- Every footrule in its entire admissible interval occurs with xi=1. -/
theorem xi_one_slice (y : ℝ) :
    (∃ C : Copula 2, C.chatterjeeXi = 1 ∧ C.spearmanFootrule = y) ↔ y ∈ Icc (-1 / 2) 1 := by
  constructor
  · rintro ⟨C, _, rfl⟩
    exact C.spearmanFootrule_mem_Icc
  · intro hy
    have hnonneg : 0 ≤ 2 / 3 * (1 - y) := by linarith [hy.2]
    let a : I := ⟨Real.sqrt (2 / 3 * (1 - y)), Real.sqrt_nonneg _,
      (Real.sqrt_le_one).mpr (by linarith [hy.1])⟩
    have ha : (a : ℝ) ^ 2 = 2 / 3 * (1 - y) := Real.sq_sqrt hnonneg
    refine ⟨rightBoundary a, (rightBoundary_coefficients a).1, ?_⟩
    rw [(rightBoundary_coefficients a).2, ha]
    ring

private theorem top_witness (C : Copula 2) :
    ∃ D : Copula 2, D.chatterjeeXi = 1 ∧ D.spearmanFootrule = C.spearmanFootrule :=
  (xi_one_slice _).mpr C.spearmanFootrule_mem_Icc

/-- Equation (26): the fixed-footrule slice contains all intermediate xi values. -/
theorem fixed_footrule_intermediate (C D : Copula 2) (he : C.spearmanFootrule = D.spearmanFootrule)
    (x : ℝ) (hC : C.chatterjeeXi ≤ x) (hD : x ≤ D.chatterjeeXi) :
    ∃ E : Copula 2, E.chatterjeeXi = x ∧ E.spearmanFootrule = C.spearmanFootrule :=
  xi_intermediate_at_coefficient Copula.spearmanFootrule Copula.spearmanFootrule_mix C D he x hC hD

/-- Every attained point extends horizontally all the way to xi=1. -/
theorem fixed_footrule_upward (C : Copula 2) (x : ℝ) (hx : C.chatterjeeXi ≤ x) (hx1 : x ≤ 1) :
    ∃ D : Copula 2, D.chatterjeeXi = x ∧ D.spearmanFootrule = C.spearmanFootrule :=
  xi_upward_at_coefficient Copula.spearmanFootrule Copula.spearmanFootrule_mix top_witness C x hx hx1

/-- Theorem 3.3: the full attainable region is convex. -/
theorem attainable_region_convex : Convex ℝ attainableRegion :=
  convex_xiCoefficientRegion Copula.spearmanFootrule Copula.spearmanFootrule_mix top_witness

/-- Exact nonnegative-footrule part of the full region, with all endpoints. -/
theorem exact_nonnegative_footrule_region (x y : ℝ) (hy : 0 ≤ y) :
    (x, y) ∈ attainableRegion ↔ y ≤ 1 ∧ y ^ 2 ≤ x ∧ x ≤ 1 := by
  constructor
  · rintro ⟨C, rfl, rfl⟩
    have h := footrule_le_sqrt_xi C
    have hs := Real.sq_sqrt C.chatterjeeXi_nonneg
    refine ⟨C.spearmanFootrule_mem_Icc.2, ?_, C.chatterjeeXi_mem_Icc.2⟩
    nlinarith [Real.sqrt_nonneg C.chatterjeeXi]
  · rintro ⟨hy1, hx, hx1⟩
    let a : I := ⟨y, hy, hy1⟩
    obtain ⟨C, hC, hCy⟩ := fixed_footrule_upward (upperBoundary a) x
      (by simpa only [xi_upperBoundary, a] using hx) hx1
    exact ⟨C, hC, hCy.trans (footrule_upperBoundary a)⟩

end Papers.Rockel2026XiFootrule
