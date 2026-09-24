import Verification.Nelsen20
import Verification.Nelsen20Conditional
import Verification.Nelsen20Tails

/-! # Tables 1–3: Nelsen 20 constructor, independence member, CI and tails -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen20_cdf {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (Verification.nelsen20 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.log (Real.exp ((u:ℝ)^(-θ))+Real.exp ((v:ℝ)^(-θ))-Real.exp 1)^(-θ⁻¹) :=
  Verification.nelsen20_cdf hθ u v

theorem nelsen20_zero : Verification.nelsen20 0 le_rfl = Copula.independence 2 :=
  Verification.nelsen20_zero

theorem nelsen20_ci (θ : ℝ) (hθ : 0 ≤ θ) : (Verification.nelsen20 θ hθ).IsCI :=
  Verification.nelsen20_isCI θ hθ

theorem nelsen20_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (Verification.nelsen20 θ hθ).HasLowerTailDependence (if θ = 0 then 0 else 1) ∧
      (Verification.nelsen20 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen20_tails θ hθ

end Papers.AnsariRockel2024
