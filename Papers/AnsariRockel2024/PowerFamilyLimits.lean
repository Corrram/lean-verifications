import Copula.Families.PowerFamilyLimits

/-! # Infinite-parameter endpoints for Nelsen 14 and Genest–Ghoudi from Table 2 -/

open Filter ProbabilityTheory
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

/-- Nelsen 14 tends pointwise to comonotonicity on the full closed square. -/
theorem nelsen14_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (Copula.nelsen14 (θ z) (hθ z)).cdf u) l
      (𝓝 ((Copula.comonotonic 2).cdf u)) :=
  Copula.tendsto_nelsen14_atTop θ hθ hlim u

/-- Genest–Ghoudi tends pointwise to comonotonicity on the full closed square. -/
theorem genestGhoudi_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (Copula.genestGhoudi (θ z) (hθ z)).cdf u) l
      (𝓝 ((Copula.comonotonic 2).cdf u)) :=
  Copula.tendsto_genestGhoudi_atTop θ hθ hlim u

end Papers.AnsariRockel2024
