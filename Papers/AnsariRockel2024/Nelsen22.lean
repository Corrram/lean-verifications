import Verification.Nelsen22Tails
import Verification.Nelsen22Limits
import Verification.Nelsen22Conditional

/-! # Nelsen 22: trigonometric copula, exact CI/TP2 classification and tails -/

open ProbabilityTheory Set Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem nelsen22_zero : Verification.nelsen22 0 (by norm_num) = Copula.independence 2 :=
  Verification.nelsen22_zero

theorem nelsen22_cdf_full {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u v : I) :
    (Verification.nelsen22 θ ⟨hθ.le,hθ1⟩).cdf ![u,v] =
      (1-Real.sin (min (Real.arcsin (1-(u:ℝ)^θ)+Real.arcsin (1-(v:ℝ)^θ)) (Real.pi/2)))^θ⁻¹ :=
  Verification.nelsen22_cdf_full hθ hθ1 u v

theorem nelsen22_cdf_printed {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (u v : I) :
    (Verification.nelsen22 θ ⟨hθ.le,hθ1⟩).cdf ![u,v] =
      if -(Real.pi/2) ≤ Real.arcsin ((u:ℝ)^θ-1)+Real.arcsin ((v:ℝ)^θ-1) then
        (1+Real.sin (Real.arcsin ((u:ℝ)^θ-1)+Real.arcsin ((v:ℝ)^θ-1)))^θ⁻¹ else 0 :=
  Verification.nelsen22_cdf_printed hθ hθ1 u v

theorem nelsen22_not_pqd {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    ¬ (Verification.nelsen22 θ ⟨hθ.le,hθ1⟩).IsPQD :=
  Verification.nelsen22_not_pqd hθ hθ1

theorem nelsen22_isCI_iff (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (Verification.nelsen22 θ hθ).IsCI ↔ θ = 0 :=
  Verification.nelsen22_isCI_iff θ hθ

theorem nelsen22_density_tp2_iff (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (Verification.nelsen22 θ hθ).HasMTP2Density ↔ θ = 0 :=
  Verification.nelsen22_density_tp2_iff θ hθ

theorem nelsen22_lowerTail (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (Verification.nelsen22 θ hθ).HasLowerTailDependence 0 :=
  Verification.nelsen22_lowerTail θ hθ

theorem nelsen22_upperTail (θ : ℝ) (hθ : θ ∈ Icc 0 1) :
    (Verification.nelsen22 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen22_upperTail θ hθ

theorem nelsen22_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ∈ Icc 0 1) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (Verification.nelsen22 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((Copula.independence 2).cdf ![u,v])) :=
  Verification.nelsen22_tendsto_zero θ hθ ht u v

theorem nelsen22_tendsto_parameter {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ∈ Icc 0 1) {η : ℝ} (hη : η ∈ Icc 0 1)
    (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (Verification.nelsen22 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((Verification.nelsen22 η hη).cdf ![u,v])) :=
  Verification.nelsen22_tendsto_parameter θ hθ hη ht u v

theorem nelsen22_isCD (θ : ℝ) (hθ : θ ∈ Icc 0 1) : (Verification.nelsen22 θ hθ).IsCD :=
  Verification.nelsen22_isCD θ hθ

theorem nelsen22_isNQD (θ : ℝ) (hθ : θ ∈ Icc 0 1) : (Verification.nelsen22 θ hθ).IsNQD :=
  (Verification.nelsen22_isCD θ hθ).isNQD

end Papers.AnsariRockel2024
