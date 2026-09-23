import Copula.Families.GumbelLimits

/-! # Gumbel–Hougaard infinite-parameter endpoint from Table 2 -/

open Filter ProbabilityTheory
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

/-- The Gumbel–Hougaard CDF converges pointwise to the upper Fréchet bound
throughout the closed square as its parameter tends to infinity. -/
theorem gumbel_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (Copula.gumbel (θ z) (hθ z)).cdf u) l
      (𝓝 ((Copula.comonotonic 2).cdf u)) :=
  Copula.tendsto_gumbel_atTop θ hθ hlim u

end Papers.AnsariRockel2024
