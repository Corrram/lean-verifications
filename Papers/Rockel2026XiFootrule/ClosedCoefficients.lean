import Papers.Rockel2026XiFootrule.LowerBound
import Verification.FootruleParameter

/-! # Proposition 3.1 and the admissible parameter in Theorem 3.3

The cubic inverse is unique on [0,2] for target footrule in [-1/2,0].
Uniqueness among all real roots would be false, as checked below.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- Proposition 3.1, evaluated from the source's exact integral definitions. -/
theorem relaxed_coefficients_closed (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    let r := 2 / (2 + μ)
    relaxedFootrule μ = -2 * r ^ 2 + 6 * r - 5 + 1 / r ∧
      relaxedXi μ = -4 * r ^ 2 + 20 * r - 17 + 2 / r - 1 / r ^ 2 - 12 * Real.log r :=
  ⟨relaxedFootrule_closed μ hμ, relaxedXi_closed μ hμ⟩

theorem relaxed_coefficients_continuous :
    ContinuousOn relaxedFootrule (Icc 0 2) ∧ ContinuousOn relaxedXi (Icc 0 2) :=
  ⟨continuousOn_relaxedFootrule, continuousOn_relaxedXi⟩

theorem relaxed_coefficients_strict_monotonicity :
    StrictAntiOn relaxedFootrule (Icc 0 2) ∧ StrictMonoOn relaxedXi (Icc 0 2) :=
  ⟨strictAntiOn_relaxedFootrule, strictMonoOn_relaxedXi⟩

theorem relaxed_coefficients_endpoints :
    relaxedFootrule 0 = 0 ∧ relaxedFootrule 2 = -1 / 2 ∧
      relaxedXi 0 = 0 ∧ relaxedXi 2 = 12 * Real.log 2 - 8 := relaxed_endpoints

/-- Every nonpositive target footrule has exactly one admissible parameter. -/
theorem footrule_inverse_unique (y : ℝ) (hy : y ∈ Icc (-1 / 2) 0) :
    ∃! μ : ℝ, μ ∈ Icc 0 2 ∧ relaxedFootrule μ = y := existsUnique_relaxedParameter y hy

theorem footrule_cubic_equivalence (y μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    relaxedFootrule μ = y ↔ μ ^ 3 - (4 + 2 * y) * μ ^ 2 - (4 + 8 * y) * μ - 8 * y = 0 :=
  relaxedFootrule_eq_iff_cubic y μ hμ

theorem footrule_cubic_unique_admissible (y : ℝ) (hy : y ∈ Icc (-1 / 2) 0) :
    ∃! μ : ℝ, μ ∈ Icc 0 2 ∧ μ ^ 3 - (4 + 2 * y) * μ ^ 2 - (4 + 8 * y) * μ - 8 * y = 0 :=
  existsUnique_footruleCubic y hy

/-- The source's phrase "unique real solution" needs the admissible interval restriction. -/
theorem footrule_cubic_not_unique_real :
    footruleCubic (-1 / 2) 2 = 0 ∧ footruleCubic (-1 / 2) (-1) = 0 ∧ (2 : ℝ) ≠ -1 :=
  Verification.footruleCubic_not_unique_real

/-- Theorem 3.2 with explicitly evaluated coefficients. -/
theorem weighted_lower_bound_closed (C : Copula 2) (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    μ * footruleClosed (relaxedParameter μ) + xiClosed (relaxedParameter μ) ≤
      μ * C.spearmanFootrule + C.chatterjeeXi := xi_footrule_closed_lower_bound C μ hμ

/-- Theorem 3.3's lower estimate at every nonpositive attainable footrule value. -/
theorem negative_footrule_lower_bound (C : Copula 2) (hy : C.spearmanFootrule ∈ Icc (-1 / 2) 0) :
    ∃! μ : ℝ, μ ∈ Icc 0 2 ∧ footruleCubic C.spearmanFootrule μ = 0 ∧
      xiClosed (relaxedParameter μ) ≤ C.chatterjeeXi := by
  obtain ⟨μ, ⟨hμ, he⟩, hu⟩ := existsUnique_footruleCubic C.spearmanFootrule hy
  refine ⟨μ, ⟨hμ, he, xi_lower_bound_of_cubic C _ μ hμ rfl he⟩, ?_⟩
  rintro ν ⟨hν, hroot, _⟩
  exact hu ν ⟨hν, hroot⟩

end Papers.Rockel2026XiFootrule
