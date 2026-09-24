import Verification.Nelsen13Tails
import Verification.Nelsen13Order
import Verification.Nelsen13Continuity
import Verification.Nelsen13Limits

/-! # Tables 1–3: Nelsen 13 constructor, endpoints, orthant order, and tails -/

open ProbabilityTheory
open scoped unitInterval
open Filter
open scoped Topology

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

theorem nelsen13_lowerOrthant_monotone {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (Verification.nelsen13 θ hθ).LowerOrthantLE (Verification.nelsen13 η hη) :=
  Verification.nelsen13_lowerOrthant_monotone hθ hη hθη

theorem nelsen13_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun z => (Verification.nelsen13 (θ z) (hθ z)).cdf ![u,v]) l
      (𝓝 ((Verification.gumbelBarnett 1).cdf ![u,v])) :=
  Verification.nelsen13_tendsto_zero θ hθ hlim u v

theorem nelsen13_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun z => (Verification.nelsen13 (θ z) (hθ z)).cdf ![u,v]) l
      (𝓝 (min (u:ℝ) (v:ℝ))) :=
  Verification.nelsen13_tendsto_atTop θ hθ hlim u v

end Papers.AnsariRockel2024
