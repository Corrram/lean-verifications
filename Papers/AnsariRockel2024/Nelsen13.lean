import Verification.Nelsen13Tails

/-! # Tables 1–3: Nelsen 13 constructor, special cases, and tails -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen13_cdf (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (Verification.nelsen13 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.exp (1-((1-Real.log (u:ℝ))^θ+(1-Real.log (v:ℝ))^θ-1)^θ⁻¹) :=
  Verification.nelsen13_cdf θ hθ u v

theorem nelsen13_zero : Verification.nelsen13 0 le_rfl = Verification.gumbelBarnett 1 :=
  Verification.nelsen13_zero

theorem nelsen13_one : Verification.nelsen13 1 zero_le_one = Copula.independence 2 :=
  Verification.nelsen13_one

theorem nelsen13_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (Verification.nelsen13 θ hθ).HasLowerTailDependence 0 ∧
      (Verification.nelsen13 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen13_tails θ hθ

end Papers.AnsariRockel2024
