import Copula.Families.Nelsen8Limits

/-! # Nelsen 8 infinite-parameter endpoint from Table 2 -/

open Filter ProbabilityTheory
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

/-- Nelsen 8 tends pointwise to Clayton at parameter one throughout the
closed square, including its zero axes. -/
theorem nelsen8_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun a => (Copula.nelsen8 (θ a) (hθ a)).cdf u) l
      (𝓝 ((Copula.clayton 2 1 (by norm_num)).cdf u)) :=
  Copula.tendsto_nelsen8_atTop θ hθ hlim u

end Papers.AnsariRockel2024
