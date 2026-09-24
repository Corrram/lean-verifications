import Verification.MaxProductConditional
import Verification.GumbelConditional
import Verification.TawnLimits

open ProbabilityTheory Copula
open scoped unitInterval

namespace Verification

theorem tawn_isCI (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) : (tawn θ hθ α β).IsCI :=
  maxProduct_independence_isCI (gumbel θ hθ) (gumbel_isCI θ hθ) α β

theorem tawn_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) (α β : I) :
    (tawn θ hθ α β).SchurBothLE (tawn η (hθ.trans hθη) α β) := by
  have ho := tawn_lowerOrthant_monotone hθ hθη α β
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (tawn_isCI θ hθ α β).1
      (tawn_isCI η (hθ.trans hθη) α β).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (tawn_isCI θ hθ α β).2
      (tawn_isCI η (hθ.trans hθη) α β).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_transpose,cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
