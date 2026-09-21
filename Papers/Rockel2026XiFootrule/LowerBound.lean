import Papers.Rockel2026XiFootrule.Definitions
import Verification.FootruleJensen

/-! # Theorem 3.2: the universal Jensen lower-bound estimate

The source profile is a relaxation and is not declared to be a copula.
The rank-like values are defined by exact integrals; their logarithmic
closed forms from Proposition 3.1 are a separate remaining obligation.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- Equations (18) and (23), with the original cutoff parameters. -/
theorem jensen_profile_formula (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I) :
    (jensenLow μ v, jensenHigh μ v) =
      if (v : ℝ) ≤ μ / (2 + μ) then (0, (v : ℝ) / (1 - v))
      else if (v : ℝ) ≤ 2 / (2 + μ) then ((v : ℝ) - μ / 2 * (1 - v), (v : ℝ) + μ / 2 * v)
      else (2 - 1 / (v : ℝ), 1) := by
  have hd : 0 < 2 + μ := by linarith [hμ.1]
  simp only [le_div_iff₀ hd]
  unfold jensenLow jensenHigh
  split_ifs <;> rfl

theorem jensen_profile_feasible (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I) :
    jensenLow μ v ∈ Icc 0 1 ∧ jensenHigh μ v ∈ Icc 0 1 ∧
      (v : ℝ) * jensenLow μ v + (1 - v) * jensenHigh μ v = v :=
  Verification.jensen_feasible μ hμ v

/-- Equation (22): the piecewise profile is a global minimizer. -/
theorem scalar_optimizer_minimum (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hm : (v : ℝ) * a + (1 - v) * b = v) :
    splitObjective μ v (jensenLow μ v) (jensenHigh μ v) ≤ splitObjective μ v a b :=
  Verification.jensen_optimal μ hμ v a b ha hb hm

/-- Uniqueness holds at every interior response threshold. -/
theorem scalar_optimizer_unique (μ : ℝ) (hμ : μ ∈ Icc 0 2) (v : I)
    (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) (a b : ℝ)
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) (hm : (v : ℝ) * a + (1 - v) * b = v) :
    splitObjective μ v a b = splitObjective μ v (jensenLow μ v) (jensenHigh μ v) ↔
      a = jensenLow μ v ∧ b = jensenHigh μ v :=
  Verification.jensen_optimal_eq_iff μ hμ v hv a b ha hb hm

/-- Equation (20) for every copula, with no density assumption. -/
theorem conditional_jensen_bound (C : Copula 2) (v : I) (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) :
    (v : ℝ) * conditionalBinLow C v ^ 2 + (1 - v) * conditionalBinHigh C v ^ 2 ≤
      ∫ u : I, C.conditionalCDF u v ^ 2 :=
  Verification.conditionalBin_jensen C v hv

theorem conditional_jensen_equality (C : Copula 2) (v : I) (hv : 0 < (v : ℝ) ∧ (v : ℝ) < 1) :
    (∫ u : I, C.conditionalCDF u v ^ 2) =
      (v : ℝ) * conditionalBinLow C v ^ 2 + (1 - v) * conditionalBinHigh C v ^ 2 ↔
      ∀ᵐ u : I, C.conditionalCDF u v =
        if u ≤ v then conditionalBinLow C v else conditionalBinHigh C v := by
  simpa only [Filter.EventuallyEq, twoBin_eq] using Verification.conditionalBin_jensen_eq_iff C v hv

/-- Equation (17): the relaxed two-bin kernel. -/
noncomputable def relaxedKernel (μ : ℝ) (u v : I) : ℝ := twoBin v (jensenLow μ v) (jensenHigh μ v) u

/-- The primitive used by the source; this is a real-valued function, not a Copula. -/
noncomputable def relaxedCDF (μ : ℝ) (u v : I) : ℝ := ∫ t in Iic u, relaxedKernel μ t v

theorem relaxedCDF_formula (μ : ℝ) (u v : I) :
    relaxedCDF μ u v = jensenHigh μ v * (u : ℝ) + (jensenLow μ v - jensenHigh μ v) * min (u : ℝ) v :=
  integral_twoBin_Iic _ _ _ _

/-- The extended coefficients use precisely the source's integral normalizations. -/
theorem relaxed_values_integral_form (μ : ℝ) :
    relaxedFootrule μ = 6 * (∫ v : I, relaxedCDF μ v v) - 2 ∧
      relaxedXi μ = 6 * (∫ v : I, ∫ u : I, relaxedKernel μ u v ^ 2) - 2 := by
  have hd (v : I) : relaxedCDF μ v v = (v : ℝ) * jensenLow μ v := by
    rw [relaxedCDF_formula, min_self]
    ring
  have hq (v : I) : (∫ u : I, relaxedKernel μ u v ^ 2) =
      (v : ℝ) * jensenLow μ v ^ 2 + (1 - v) * jensenHigh μ v ^ 2 := by
    change (∫ u : I, twoBin v (jensenLow μ v) (jensenHigh μ v) u ^ 2) = _
    rw [twoBin_sq, integral_twoBin]
  constructor
  · simp_rw [hd]
    rfl
  · simp_rw [hq]
    rfl

/-- Theorem 3.2 over the parameter interval specified in Section 3.1. -/
theorem weighted_lower_bound (C : Copula 2) (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    μ * relaxedFootrule μ + relaxedXi μ ≤ μ * C.spearmanFootrule + C.chatterjeeXi :=
  Verification.xi_footrule_relaxed_lower_bound C μ hμ

/-- The parameterized lower-bound consequence used in Theorem 3.3. -/
theorem xi_lower_bound_at_relaxed_footrule (C : Copula 2) (μ : ℝ) (hμ : μ ∈ Icc 0 2)
    (hC : C.spearmanFootrule = relaxedFootrule μ) : relaxedXi μ ≤ C.chatterjeeXi :=
  Verification.xi_lower_bound_at_relaxed_footrule C μ hμ hC

/-- The relaxed family cannot be treated as an attaining copula family:
at μ=2 its primitive decreases in the second coordinate. -/
theorem relaxed_family_not_copula :
    ¬∃ C : Copula 2, ∀ u v : I, C.cdf ![u, v] = relaxedCDF 2 u v := by
  rintro ⟨C, hC⟩
  let u : I := ⟨3 / 10, by constructor <;> norm_num⟩
  let v : I := ⟨1 / 5, by constructor <;> norm_num⟩
  have hm : C.cdf ![u, v] ≤ C.cdf ![u, u] := C.monotone_cdf (by
    intro i
    fin_cases i <;> norm_num [u, v])
  rw [hC u v, hC u u, relaxedCDF_formula, relaxedCDF_formula] at hm
  norm_num [jensenLow, jensenHigh, u, v] at hm

end Papers.Rockel2026XiFootrule
