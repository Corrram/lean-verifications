import Papers.Rockel2026XiFootrule.SIRegion
import Verification.StochasticFootruleEquality

/-! # Proposition 2.2: complete equality classification in the SI class

The source representation uses open intervals and equality almost
everywhere in both variables. The cut functions are nondecreasing and
measurable; the middle level is measurable. Singular copulas are included.
The proof uses an elementary nonnegative moment defect rather than
Lebesgue-Stieltjes integration by parts.
-/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- Equation (11), including the source's open-interval convention. -/
noncomputable def siEqualityProfile (A B a u : I) : ℝ :=
  (if u < A then 1 else 0) + (a : ℝ) * (if A < u ∧ u < B then 1 else 0)

theorem si_equality_iff_diagonal_moments (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanFootrule ↔
      ∀ᵐ v : I, (∫ u : I, C.conditionalCDF u v ^ 2) = C.cdf ![v, v] :=
  Verification.ae_diagonal_moment_eq_iff C hC

/-- Explicit witnesses for the existential functions in Proposition 2.2. -/
theorem si_equality_canonical_parameters (C : Copula 2) (hC : C.IsSI)
    (he : C.chatterjeeXi = C.spearmanFootrule) :
    Monotone (conditionalOneCut C) ∧ Monotone (conditionalPositiveCut C) ∧
      Measurable (conditionalOneCut C) ∧ Measurable (conditionalPositiveCut C) ∧
      Measurable (conditionalMiddle C) ∧
      (∀ v, conditionalOneCut C v ≤ v ∧ v ≤ conditionalPositiveCut C v) ∧
      ∀ᵐ v : I, ∀ᵐ u : I, C.conditionalCDF u v =
        siEqualityProfile (conditionalOneCut C v) (conditionalPositiveCut C v) (conditionalMiddle C v) u := by
  refine ⟨conditionalOneCut_monotone C, conditionalPositiveCut_monotone C,
    (conditionalOneCut_monotone C).measurable, (conditionalPositiveCut_monotone C).measurable,
    measurable_conditionalMiddle C, fun v => ⟨conditionalOneCut_le C v, le_conditionalPositiveCut C v⟩, ?_⟩
  filter_upwards [(ae_diagonal_moment_eq_iff C hC).mp he] with v hv
  exact (conditionalCDF_threeLevel_of_diagonal_moment_eq C hC v hv).trans
    (threeLevel_eq_open_ae _ _ ((conditionalOneCut_le C v).trans (le_conditionalPositiveCut C v)) _)

/-- Proposition 2.2 in the conditional-CDF convention. -/
theorem si_equality_iff_conditional_threeLevel (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanFootrule ↔
      ∃ A B a : I → I, Monotone A ∧ Monotone B ∧ Measurable A ∧ Measurable B ∧
        Measurable a ∧ ∀ᵐ v : I, ∀ᵐ u : I,
          C.conditionalCDF u v = siEqualityProfile (A v) (B v) (a v) u :=
  Verification.si_xi_eq_footrule_iff_threeLevel C hC

/-- Proposition 2.2 in the source's first partial derivative convention. -/
theorem si_equality_iff_derivative_threeLevel (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanFootrule ↔
      ∃ A B a : I → I, Monotone A ∧ Monotone B ∧ Measurable A ∧ Measurable B ∧
        Measurable a ∧ ∀ᵐ v : I, ∀ᵐ u : I,
          deriv (Copula.cdfSection C v) (u : ℝ) = siEqualityProfile (A v) (B v) (a v) u :=
  Verification.si_xi_eq_footrule_iff_derivative_threeLevel C hC

end Papers.Rockel2026XiFootrule
