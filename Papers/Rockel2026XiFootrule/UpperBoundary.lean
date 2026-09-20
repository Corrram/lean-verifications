import Papers.Rockel2026XiFootrule.Definitions
import Copula.Rank.ChatterjeeCrossMixture

/-! # The upper xi-footrule boundary

Theorem 2.1 of arXiv:2509.07232v1, in the conditional-CDF formulation.
The squared distance to `(1-a) Π + a M` proves the bound and its unique
equality case. No density, stochastic monotonicity, or optimization assumption
is imposed on the copula. See COVERAGE.md for the source conventions.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

theorem xi_upperBoundary (a : I) : (upperBoundary a).chatterjeeXi = (a : ℝ) ^ 2 := by
  simp [upperBoundary, Copula.chatterjeeXi_mix_independence]

theorem footrule_upperBoundary (a : I) :
    (upperBoundary a).spearmanFootrule = (a : ℝ) := by
  simp [upperBoundary, Copula.spearmanFootrule_mix]

/-- The exact nonnegative defect; vanishing characterizes the extremizer. -/
theorem distance_to_upperBoundary (C : Copula 2) (a : I) :
    6 * C.conditionalCDFDistanceSq (upperBoundary a) =
      C.chatterjeeXi + (a : ℝ) ^ 2 - 2 * (a : ℝ) * C.spearmanFootrule := by
  rw [Copula.conditionalCDFDistanceSq_eq_cross, xi_upperBoundary]
  simp only [upperBoundary, Copula.chatterjeeCross_mix_right,
    Copula.chatterjeeCross_comonotonic, Copula.chatterjeeCross_independence,
    mul_zero, add_zero]
  ring

/-- Theorem 2.1: the universal upper bound, including singular copulas. -/
theorem footrule_le_sqrt_xi (C : Copula 2) :
    C.spearmanFootrule ≤ Real.sqrt C.chatterjeeXi := by
  by_cases hp : 0 ≤ C.spearmanFootrule
  · let a : I := ⟨C.spearmanFootrule, hp, C.spearmanFootrule_mem_Icc.2⟩
    have hd := distance_to_upperBoundary C a
    have hn := C.conditionalCDFDistanceSq_nonneg (upperBoundary a)
    have hs := Real.sq_sqrt C.chatterjeeXi_nonneg
    have hr := Real.sqrt_nonneg C.chatterjeeXi
    change 6 * C.conditionalCDFDistanceSq (upperBoundary a) =
      C.chatterjeeXi + C.spearmanFootrule ^ 2 -
        2 * C.spearmanFootrule * C.spearmanFootrule at hd
    nlinarith
  · exact (le_of_not_ge hp).trans (Real.sqrt_nonneg _)

/-- The parameter that realizes a prescribed xi. -/
noncomputable def boundaryParameter (x : I) : I :=
  ⟨Real.sqrt (x : ℝ), Real.sqrt_nonneg _,
    (Real.sqrt_le_one).2 x.property.2⟩

/-- Theorem 2.1: the maximum is attained for every `x ∈ [0,1]`. -/
theorem upperBoundary_attains (x : I) :
    (upperBoundary (boundaryParameter x)).chatterjeeXi = (x : ℝ) ∧
    (upperBoundary (boundaryParameter x)).spearmanFootrule = Real.sqrt (x : ℝ) := by
  rw [xi_upperBoundary, footrule_upperBoundary]
  exact ⟨Real.sq_sqrt x.property.1, rfl⟩

/-- Theorem 2.1: the equality case identifies the unique copula, also at xi=0,1. -/
theorem upperBoundary_unique (x : I) (C : Copula 2) (hx : C.chatterjeeXi = (x : ℝ)) :
    C.spearmanFootrule = Real.sqrt (x : ℝ) ↔ C = upperBoundary (boundaryParameter x) := by
  constructor
  · intro hp
    have hd := distance_to_upperBoundary C (boundaryParameter x)
    change 6 * C.conditionalCDFDistanceSq (upperBoundary (boundaryParameter x)) =
      C.chatterjeeXi + Real.sqrt (x : ℝ) ^ 2 -
        2 * Real.sqrt (x : ℝ) * C.spearmanFootrule at hd
    rw [hx, hp, Real.sq_sqrt x.property.1] at hd
    apply (C.conditionalCDFDistanceSq_eq_zero_iff _).1
    nlinarith [Real.sq_sqrt x.property.1]
  · rintro rfl
    exact (upperBoundary_attains x).2

/-- Theorem 2.1 as a maximum statement together with its unique maximizer. -/
theorem maximal_footrule (x : I) :
    (upperBoundary (boundaryParameter x)).chatterjeeXi = (x : ℝ) ∧
    (upperBoundary (boundaryParameter x)).spearmanFootrule = Real.sqrt (x : ℝ) ∧
    ∀ C : Copula 2, C.chatterjeeXi = (x : ℝ) →
      C.spearmanFootrule ≤ Real.sqrt (x : ℝ) ∧
      (C.spearmanFootrule = Real.sqrt (x : ℝ) ↔ C = upperBoundary (boundaryParameter x)) := by
  refine ⟨(upperBoundary_attains x).1, (upperBoundary_attains x).2, ?_⟩
  intro C hx
  exact ⟨hx ▸ footrule_le_sqrt_xi C, upperBoundary_unique x C hx⟩

/-- The sharp gap stated after Theorem 2.1 and in the Fréchet row of Table 1. -/
theorem footrule_sub_xi_le (C : Copula 2) :
    C.spearmanFootrule - C.chatterjeeXi ≤ 1 / 4 := by
  have hd := distance_to_upperBoundary C Copula.unitHalf
  have hn := C.conditionalCDFDistanceSq_nonneg (upperBoundary Copula.unitHalf)
  change 6 * C.conditionalCDFDistanceSq (upperBoundary Copula.unitHalf) =
    C.chatterjeeXi + (1 / 2 : ℝ) ^ 2 - 2 * (1 / 2) * C.spearmanFootrule at hd
  norm_num at hd
  linarith

/-- The exact equality case for the gap; numerical rows of Table 1 are not claimed. -/
theorem footrule_sub_xi_eq_iff (C : Copula 2) :
    C.spearmanFootrule - C.chatterjeeXi = 1 / 4 ↔ C = upperBoundary Copula.unitHalf := by
  have hd := distance_to_upperBoundary C Copula.unitHalf
  change 6 * C.conditionalCDFDistanceSq (upperBoundary Copula.unitHalf) =
    C.chatterjeeXi + (1 / 2 : ℝ) ^ 2 - 2 * (1 / 2) * C.spearmanFootrule at hd
  norm_num at hd
  rw [← C.conditionalCDFDistanceSq_eq_zero_iff (upperBoundary Copula.unitHalf)]
  constructor <;> intro h <;> linarith

end Papers.Rockel2026XiFootrule
