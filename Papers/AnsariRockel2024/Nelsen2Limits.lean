import Copula.Families.Nelsen2Limits

/-! # Nelsen 2 infinite-parameter endpoint from Table 2 -/

open Filter ProbabilityTheory
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

/-- The Nelsen 2 copula tends pointwise to the upper Fréchet bound on the
entire closed square as its parameter tends to infinity. -/
theorem nelsen2_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (Copula.nelsen2 (θ a) (hθ a)).cdf u) l
      (𝓝 ((Copula.comonotonic 2).cdf u)) :=
  Copula.tendsto_nelsen2_atTop θ hθ hlim u

end Papers.AnsariRockel2024