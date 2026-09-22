import Papers.AnsariRockel2026RhoFootrule.CorrelationRatio
import Verification.FoldedUniformRank
import Verification.FoldedUniformLaw
import Verification.CorrelationRatioMixture

/-! # Example 2.8 with the source's exact folded-uniform joint law -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

noncomputable abbrev foldedExample := foldedUniform

/-- X=abs(2U-1) and Y=U, with U uniform, exactly as in the source. -/
theorem foldedExample_joint_law :
    foldedExample.toMeasure = (volume : Measure I).map (fun u => ![foldRank u,u]) :=
  foldedUniform_joint_law

theorem foldedExample_uniform_predictor : MeasurePreserving foldRank (volume : Measure I) volume :=
  foldRank_measurePreserving

/-- The conditional distribution is equally supported at (1-r)/2 and (1+r)/2. -/
theorem foldedExample_conditionalCDF (v : I) :
    (fun u => foldedExample.conditionalCDF u v) =ᵐ[volume] foldKernel v :=
  foldedUniform_conditionalCDF v

theorem foldedExample_conditionalMean :
    conditionalMean foldedExample =ᵐ[volume] fun _ => (1/2 : ℝ) :=
  foldedUniform_conditionalMean

theorem foldedExample_coefficients :
    foldedExample.chatterjeeXi = 1/4 ∧ copulaCorrelationRatio foldedExample = 0 :=
  ⟨foldedUniform_xi,foldedUniform_correlationRatio⟩

/-- An actual copula attains the bottom of the quarter-xi slice. -/
theorem quarter_xi_zero_ratio_attained :
    ∃ C : Copula 2, C.chatterjeeXi = 1/4 ∧ copulaCorrelationRatio C = 0 :=
  ⟨foldedExample,foldedExample_coefficients⟩

/-- The entire horizontal part of the constructive lower inner curve (44). -/
theorem zero_ratio_interval_attained (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1/4)) :
    ∃ C : Copula 2, C.chatterjeeXi = x ∧ copulaCorrelationRatio C = 0 := by
  have hs := Real.sq_sqrt hx.1
  have hn := Real.sqrt_nonneg x
  let a : I := ⟨2*Real.sqrt x,by constructor <;> nlinarith [hx.2]⟩
  refine ⟨foldedExample.mix (Copula.independence 2) a,?_,?_⟩
  · rw [Copula.chatterjeeXi_mix_independence,foldedExample_coefficients.1]
    dsimp [a]
    nlinarith only [hs]
  · change correlationRatio (foldedExample.mix (Copula.independence 2) a) = 0
    rw [correlationRatio_mix_independence,foldedUniform_correlationRatio,mul_zero]

end Papers.AnsariRockel2026RhoFootrule
