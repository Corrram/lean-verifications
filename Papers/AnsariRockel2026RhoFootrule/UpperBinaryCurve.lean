import Papers.AnsariRockel2026RhoFootrule.CorrelationRatio
import Verification.FlatTent

/-! # The binary building block of the upper inner curve -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

/-- Predictor reflection of the source binary model; both directional coefficients are unchanged. -/
noncomputable def upperBinary (a : I) : Copula 2 := twoStrip (flatTentDisplacement a)

/-- The two conditional distribution functions are v plus or minus the flat-topped tent. -/
theorem upperBinary_conditional_distribution (a v : I) :
    (fun u => (upperBinary a).conditionalCDF u v) =ᵐ[volume]
      fun u => if u ≤ Copula.unitHalf then (v : ℝ)+flatTent a v else (v : ℝ)-flatTent a v :=
  conditionalCDF_twoStrip (flatTentDisplacement a) v

/-- The exact conditional means of the two halves. -/
theorem upperBinary_conditionalMean (a : I) (ha : (a : ℝ) ≤ 1/2) :
    conditionalMean (upperBinary a) =ᵐ[volume]
      fun u => if u ≤ Copula.unitHalf then 1/2-(a : ℝ)*(1-(a : ℝ)) else 1/2+(a : ℝ)*(1-(a : ℝ)) := by
  have h := conditionalMean_twoStrip (flatTentDisplacement a)
  change conditionalMean (upperBinary a) =ᵐ[volume]
    fun u => if u ≤ Copula.unitHalf then 1/2-(∫ v : I, flatTent a v) else 1/2+(∫ v : I, flatTent a v) at h
  simpa only [integral_flatTent a ha] using h

/-- The n=1 branch in equations (45) and (120). -/
theorem upperBinary_coefficients (a : I) (ha : (a : ℝ) ≤ 1/2) :
    (upperBinary a).chatterjeeXi = 2*(a : ℝ)^2*(3-4*(a : ℝ)) ∧
      copulaCorrelationRatio (upperBinary a) = 12*(a : ℝ)^2*(1-(a : ℝ))^2 :=
  ⟨xi_flatTent a ha,correlationRatio_flatTent a ha⟩

/-- Each parameter on the first upper branch is realized by an actual copula. -/
theorem upper_binary_attained (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) (1/2)) :
    ∃ C : Copula 2, C.chatterjeeXi = 2*a^2*(3-4*a) ∧ copulaCorrelationRatio C = 12*a^2*(1-a)^2 := by
  let t : I := ⟨a,ha.1,by linarith [ha.2]⟩
  exact ⟨upperBinary t,upperBinary_coefficients t ha.2⟩

end Papers.AnsariRockel2026RhoFootrule
