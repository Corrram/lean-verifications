import Verification.GumbelConditional
import Verification.JoeConditional

/-! # Table 3: Gumbel–Hougaard and Joe conditional increase -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

theorem gumbel_ci (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.gumbel θ hθ).IsCI :=
  Verification.gumbel_isCI θ hθ

theorem gumbel_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (Copula.gumbel θ hθ).SchurBothLE (Copula.gumbel η hη) :=
  Verification.gumbel_schur_monotone hθ hη hθη

theorem joe_ci (θ : ℝ) (hθ : 1 ≤ θ) : (Copula.joe θ hθ).IsCI :=
  Verification.joe_isCI θ hθ

end Papers.AnsariRockel2024
