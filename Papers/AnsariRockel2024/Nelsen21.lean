import Verification.Nelsen21Tails
import Verification.Nelsen21Limits
import Verification.Nelsen21Order
import Verification.Nelsen21Schur

/-! # Nelsen 21: measure constructor, printed CDF, and countermonotonic endpoint -/

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem nelsen21_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Verification.nelsen21 θ hθ).cdf ![u,v] =
      1-(1-(max 0 ((1-(1-(u:ℝ))^θ)^θ⁻¹+(1-(1-(v:ℝ))^θ)^θ⁻¹-1))^θ)^θ⁻¹ :=
  Verification.nelsen21_cdf_full θ hθ u v

theorem nelsen21_one : Verification.nelsen21 1 (by norm_num) = Copula.countermonotonic :=
  Verification.nelsen21_one

theorem nelsen21_lowerTail (θ : ℝ) (hθ : 1 ≤ θ) :
    (Verification.nelsen21 θ hθ).HasLowerTailDependence 0 :=
  Verification.nelsen21_lowerTail θ hθ

theorem nelsen21_upperTail (θ : ℝ) (hθ : 1 ≤ θ) :
    (Verification.nelsen21 θ hθ).HasUpperTailDependence (2-(2:ℝ)^θ⁻¹) :=
  Verification.nelsen21_upperTail θ hθ

theorem nelsen21_not_pqd (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬ (Verification.nelsen21 θ hθ).IsPQD :=
  Verification.nelsen21_not_pqd θ hθ

theorem nelsen21_not_ci (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬ (Verification.nelsen21 θ hθ).IsCI :=
  Verification.nelsen21_not_ci θ hθ

theorem nelsen21_not_density_tp2 (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬ (Verification.nelsen21 θ hθ).HasMTP2Density :=
  Verification.nelsen21_not_density_tp2 θ hθ

theorem nelsen21_isCD_iff (θ : ℝ) (hθ : 1 ≤ θ) :
    (Verification.nelsen21 θ hθ).IsCD ↔ θ = 1 :=
  Verification.nelsen21_isCD_iff θ hθ

theorem nelsen21_isNQD_iff (θ : ℝ) (hθ : 1 ≤ θ) :
    (Verification.nelsen21 θ hθ).IsNQD ↔ θ = 1 :=
  Verification.nelsen21_isNQD_iff θ hθ

theorem nelsen21_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (Verification.nelsen21 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((Copula.comonotonic 2).cdf ![u,v])) :=
  Verification.nelsen21_tendsto_atTop θ hθ ht u v

theorem nelsen21_tendsto_parameter {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) {η : ℝ} (hη : 1 ≤ η) (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (Verification.nelsen21 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((Verification.nelsen21 η hη).cdf ![u,v])) :=
  Verification.nelsen21_tendsto_parameter θ hθ hη ht u v

theorem nelsen21_tendsto_one {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (ht : Tendsto θ l (𝓝 1)) (u v : I) :
    Tendsto (fun a => (Verification.nelsen21 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 (Copula.countermonotonic.cdf ![u,v])) :=
  Verification.nelsen21_tendsto_one θ hθ ht u v

theorem nelsen21_lowerOrthant_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) :
    (Verification.nelsen21 θ hθ).LowerOrthantLE (Verification.nelsen21 η (hθ.trans hθη)) :=
  Verification.nelsen21_lowerOrthant_monotone hθ hθη

theorem nelsen21_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 1 ≤ θ) (hθη : θ ≤ η),
      (Verification.nelsen21 θ hθ).SchurLE (Verification.nelsen21 η (hθ.trans hθη))) :=
  Verification.nelsen21_not_schur_monotone

theorem nelsen21_not_schur_antitone :
    ¬ (∀ (θ η : ℝ) (hθ : 1 ≤ θ) (hθη : θ ≤ η),
      (Verification.nelsen21 η (hθ.trans hθη)).SchurLE (Verification.nelsen21 θ hθ)) :=
  Verification.nelsen21_not_schur_antitone

end Papers.AnsariRockel2024
