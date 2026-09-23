import Copula.Families.JoeLimits

/-! # Joe infinite-parameter endpoint from Table 2 -/

open Filter ProbabilityTheory
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

/-- The Joe CDF converges pointwise to the upper Fréchet bound throughout
the closed square as its parameter tends to infinity. -/
theorem joe_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 1 ≤ θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (Copula.joe (θ z) (hθ z)).cdf u) l
      (𝓝 ((Copula.comonotonic 2).cdf u)) :=
  Copula.tendsto_joe_atTop θ hθ hlim u

end Papers.AnsariRockel2024
