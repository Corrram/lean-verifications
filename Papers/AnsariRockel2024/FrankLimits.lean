import Verification.FrankLimits

/-! # Table 1: both infinite-parameter Frank endpoints -/

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem frank_cdf_lower_bound (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    min (u:ℝ) (v:ℝ)-Real.log 2/θ ≤ (Copula.frank θ hθ).cdf ![u,v] :=
  Verification.frank_cdf_lower_bound θ hθ u v

theorem frank_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 < θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (Copula.frank (θ z) (hθ z)).cdf u) l
      (𝓝 ((Copula.comonotonic 2).cdf u)) :=
  Verification.tendsto_frank_atTop θ hθ hlim u

theorem frank_tendsto_atBot {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, θ z < 0) (hlim : Tendsto θ l atBot) (u : Fin 2 → I) :
    Tendsto (fun z => (Copula.frankNegative (θ z) (hθ z)).cdf u) l
      (𝓝 (Copula.countermonotonic.cdf u)) :=
  Verification.tendsto_frankNegative_atBot θ hθ hlim u

end Papers.AnsariRockel2024
