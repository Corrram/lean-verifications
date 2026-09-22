import Papers.Rockel2026XiBlest.SectionFormulas
import Verification.QuadraticMeanDerivative

/-! # The normalization derivative and all four substitutions in Lemma 4.2 -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiBlest

theorem normalizationMean_eq_clampedSquareMean (b : ℝ) : normalizationMean b=clampedSquareMean b := by
  funext q
  unfold normalizationMean clampedSquareMean
  simpa only [unitInterval.coe_symm_eq] using
    integral_unit_reflection (fun x : I => unitClamp (b*((x : ℝ)^2-q)))

theorem normalizationMean_hasDerivAt (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1) :
    HasDerivAt (normalizationMean b) (-b*(quadraticUpper b q-quadraticLower q)) q := by
  rw [normalizationMean_eq_clampedSquareMean]
  exact clampedSquareMean_hasDerivAt b q hb hq

/-- Lemma 4.2(i), including the zero-radius endpoint. -/
theorem substitution_upper (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqneg : q ≤ 0) (hR : Real.sqrt (q+1/b) ≤ 1) :
    -(2*Real.sqrt (q+1/b))*deriv (normalizationMean b) q=2*b*(Real.sqrt (q+1/b))^2 := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_left hqneg,Real.sqrt_zero,min_eq_right hR,sub_zero]
  ring

/-- Lemma 4.2(ii). -/
theorem substitution_unclamped (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqneg : q ≤ 0) (hR : 1 ≤ Real.sqrt (q+1/b)) :
    -(2*Real.sqrt (q+1/b))*deriv (normalizationMean b) q=2*b*Real.sqrt (q+1/b) := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_left hqneg,Real.sqrt_zero,min_eq_left hR,sub_zero]
  ring

/-- Lemma 4.2(iii), including q=0. -/
theorem substitution_double (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqpos : 0 ≤ q) (hR : Real.sqrt (q+1/b) ≤ 1) :
    -(2*Real.sqrt (q+1/b))*deriv (normalizationMean b) q=
      1+b*(Real.sqrt (q+1/b)-Real.sqrt q)^2 := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_right hqpos,min_eq_right hR]
  have hs := Real.sq_sqrt hqpos
  have hS := Real.sq_sqrt (show 0 ≤ q+1/b by positivity)
  have hi : b*(1/b)=1 := by field_simp
  have hd : (Real.sqrt (q+1/b))^2-(Real.sqrt q)^2=1/b := by linarith
  nlinarith [congrArg (fun x : ℝ => b*x) hd]

/-- Lemma 4.2(iv), including both boundary radii. -/
theorem substitution_lower (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (hqpos : 0 ≤ q) (hR : 1 ≤ Real.sqrt (q+1/b)) :
    -(2*Real.sqrt q)*deriv (normalizationMean b) q=2*b*Real.sqrt q*(1-Real.sqrt q) := by
  rw [(normalizationMean_hasDerivAt b q hb hq).deriv]
  simp only [quadraticUpper,quadraticLower,max_eq_right hqpos,min_eq_left hR]
  ring

end Papers.Rockel2026XiBlest
