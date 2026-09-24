import Verification.TawnLimits

/-! # Tawn limits, shape order, and the TP2 Gumbel subfamily -/

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem tawn_tendsto_atTop {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (ht : Tendsto θ l atTop) (α β : I) (u : Fin 2 → I) :
    Tendsto (fun a => (Copula.tawn (θ a) (hθ a) α β).cdf u) l
      (𝓝 ((Copula.marshallOlkin α β).cdf u)) :=
  Verification.tawn_tendsto_atTop θ hθ ht α β u

theorem tawn_lowerOrthant_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) (α β : I) :
    (Copula.tawn θ hθ α β).LowerOrthantLE (Copula.tawn η (hθ.trans hθη) α β) :=
  Verification.tawn_lowerOrthant_monotone hθ hθη α β

theorem tawn_tendsto_parameter {A : Type*} {l : Filter A} (θ : A → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) {η : ℝ} (hη : 1 ≤ η) (ht : Tendsto θ l (𝓝 η)) (α β u v : I) :
    Tendsto (fun a => (Copula.tawn (θ a) (hθ a) α β).cdf ![u,v]) l
      (𝓝 ((Copula.tawn η hη α β).cdf ![u,v])) :=
  Verification.tawn_tendsto_parameter θ hθ hη ht α β u v

theorem tawn_one_one_density_tp2 (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.tawn θ hθ 1 1).HasMTP2Density :=
  Verification.tawn_one_one_density_tp2 θ hθ

theorem tawn_one_one_not_independence {θ : ℝ} (hθ : 1 < θ) :
    Copula.tawn θ hθ.le 1 1 ≠ Copula.independence 2 :=
  Verification.tawn_one_one_not_independence hθ

theorem tawn_printed_tp2_exclusion_false :
    ¬ (∀ (θ : ℝ) (hθ : 1 ≤ θ) (α β : I), Copula.tawn θ hθ α β ≠ Copula.independence 2 →
      ¬ (Copula.tawn θ hθ α β).HasMTP2Density) :=
  Verification.tawn_printed_tp2_exclusion_false

end Papers.AnsariRockel2024
