import Papers.AnsariRockel2026RhoFootrule.FoldedExample
import Verification.PartialRevealRank

/-! # The full constructive lower curve in equation (44) -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

/-- The source lower inner curve, written with sqrt-cubed instead of a real exponent. -/
noncomputable def lowerInnerRatio (x : ℝ) : ℝ :=
  if x ≤ 1/4 then 0 else (Real.sqrt ((4*x-1)/3))^3

/-- The square-root convention agrees with the displayed exponent 3/2. -/
theorem lowerInnerRatio_formula (x : ℝ) (hx : 1/4 ≤ x) :
    lowerInnerRatio x = ((4*x-1)/3)^(3/2 : ℝ) := by
  have hz : 0 ≤ (4*x-1)/3 := by linarith
  by_cases h : x ≤ 1/4
  · have he : x = 1/4 := le_antisymm h hx
    subst x
    norm_num [lowerInnerRatio]
  · rw [lowerInnerRatio,ite_eq_right h,Real.sqrt_eq_rpow,← Real.rpow_mul_natCast hz]
    norm_num

/-- The constructed family reveals the central interval and pairs the remaining ranks. -/
theorem partialReveal_conditional_distribution (t v : I) :
    (fun u => (partialReveal t).conditionalCDF u v) =ᵐ[volume] partialRevealKernel t v :=
  partialReveal_conditionalCDF t v

/-- The exact parameterized coefficient path includes t=0 and t=1. -/
theorem partialReveal_coefficients (t : I) :
    (partialReveal t).chatterjeeXi = (1+3*(t : ℝ)^2)/4 ∧
      copulaCorrelationRatio (partialReveal t) = (t : ℝ)^3 :=
  ⟨partialReveal_xi t,partialReveal_correlationRatio t⟩

/-- Every point of the curved lower inner boundary is attained by an actual copula. -/
theorem curved_lower_inner_attained (x : ℝ) (hx : x ∈ Set.Icc (1/4 : ℝ) 1) :
    ∃ C : Copula 2, C.chatterjeeXi = x ∧ copulaCorrelationRatio C = ((4*x-1)/3)^(3/2 : ℝ) := by
  have hz : 0 ≤ (4*x-1)/3 := by linarith [hx.1]
  have hs := Real.sq_sqrt hz
  have hn := Real.sqrt_nonneg ((4*x-1)/3)
  let t : I := ⟨Real.sqrt ((4*x-1)/3),hn,by nlinarith [hx.2]⟩
  refine ⟨partialReveal t,?_,?_⟩
  · rw [partialReveal_xi]
    dsimp [t]
    nlinarith only [hs]
  · change correlationRatio (partialReveal t) = ((4*x-1)/3)^(3/2 : ℝ)
    rw [partialReveal_correlationRatio]
    dsimp [t]
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul_natCast hz]
    norm_num

/-- Equation (44): the complete lower inner curve, including the horizontal segment. -/
theorem lower_inner_attained (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ C : Copula 2, C.chatterjeeXi = x ∧ copulaCorrelationRatio C = lowerInnerRatio x := by
  by_cases h : x ≤ 1/4
  · rw [lowerInnerRatio,ite_eq_left h]
    exact zero_ratio_interval_attained x ⟨hx.1,h⟩
  · rw [lowerInnerRatio_formula x (le_of_not_ge h)]
    exact curved_lower_inner_attained x ⟨le_of_not_ge h,hx.2⟩

end Papers.AnsariRockel2026RhoFootrule
