import Papers.AnsariRockel2026RhoFootrule.CorrelationRatio
import Verification.ConditionalQuantitativeGap

/-! # A quantitative non-sharpness certificate for Example 2.9 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2026RhoFootrule

/-- A universal improvement using the endpoint restrictions of conditional CDFs. -/
theorem correlationRatio_uniform_improvement (C : Copula 2) :
    (21/20 : ℝ)*copulaCorrelationRatio C ≤ 2*C.chatterjeeXi+3/250 :=
  Verification.correlationRatio_quantitative_bound C

/-- The whole quarter-xi slice stays a positive distance below eta=1/2. -/
theorem quarter_xi_uniform_gap (C : Copula 2) (h : C.chatterjeeXi = 1/4) :
    copulaCorrelationRatio C ≤ 256/525 := by
  have hb := correlationRatio_uniform_improvement C
  rw [h] at hb
  linarith only [hb]

/-- Non-sharpness holds even for the supremum; no compactness premise is required. -/
theorem quarter_xi_uniform_separation :
    ∃ e : ℝ, 0 < e ∧ ∀ C : Copula 2, C.chatterjeeXi = 1/4 →
      copulaCorrelationRatio C ≤ 1/2-e := by
  refine ⟨13/1050,by norm_num,?_⟩
  intro C h
  have hb := quarter_xi_uniform_gap C h
  linarith only [hb]

end Papers.AnsariRockel2026RhoFootrule
