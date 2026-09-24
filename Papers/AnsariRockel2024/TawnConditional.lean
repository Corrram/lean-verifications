import Verification.TawnConditional

/-! # Table 5: Tawn conditional increase and both directional Schur orders -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem tawn_ci (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) : (Copula.tawn θ hθ α β).IsCI :=
  Verification.tawn_isCI θ hθ α β

theorem tawn_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) (α β : I) :
    (Copula.tawn θ hθ α β).SchurBothLE (Copula.tawn η (hθ.trans hθη) α β) :=
  Verification.tawn_schur_monotone hθ hθη α β

/-- The closure argument used for the asymmetric logistic family includes all weight endpoints. -/
theorem maxProduct_independence_ci (C : Copula 2) (hC : C.IsCI) (α β : I) :
    (Copula.maxProduct C (Copula.independence 2) ![α,β]).IsCI :=
  Verification.maxProduct_independence_isCI C hC α β

end Papers.AnsariRockel2024
