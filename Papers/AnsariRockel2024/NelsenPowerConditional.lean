import Verification.BB1Conditional
import Verification.SchurOrthantEquivalence
import Copula.Dependence.Nelsen12
import Copula.Order.SymmetricSchur

/-! # Table 3: conditional increase for Nelsen 12 and 14 -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen12_ci (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.nelsen12 θ hθ).IsCI :=
  Verification.nelsen12_isCI θ hθ

theorem nelsen14_ci (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.nelsen14 θ hθ).IsCI :=
  Verification.nelsen14_isCI θ hθ

theorem nelsen12_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (Copula.nelsen12 θ hθ).SchurBothLE (Copula.nelsen12 η hη) := by
  have ho := Copula.lowerOrthantLE_nelsen12 hθ hη hθη
  constructor
  · exact (Verification.schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen12_ci θ hθ).1
      (nelsen12_ci η hη).1).mpr ho
  · apply (Verification.schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen12_ci θ hθ).2
      (nelsen12_ci η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, Copula.cdf_transpose, Copula.cdf_transpose]
    exact ho ![x 1,x 0]

end Papers.AnsariRockel2024
