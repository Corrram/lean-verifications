import Verification.Nelsen11Continuity
import Verification.Nelsen11Dependence
import Verification.Nelsen11Order

/-! # Tables 1–3: Nelsen 11 as an actual copula measure -/

open ProbabilityTheory
open scoped unitInterval
open Filter
open scoped Topology

namespace Papers.AnsariRockel2024

theorem nelsen11_cdf (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1/2) (u v : I) :
    (Verification.nelsen11 θ hθ.le hθ1).cdf ![u,v] =
      (max 0 ((u:ℝ)^θ*(v:ℝ)^θ-2*(1-(u:ℝ)^θ)*(1-(v:ℝ)^θ)))^θ⁻¹ :=
  Verification.nelsen11_cdf θ hθ hθ1 u v

theorem nelsen11_zero : Verification.nelsen11 0 le_rfl (by norm_num) = Copula.independence 2 :=
  Verification.nelsen11_zero

theorem nelsen11_nqd (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (Verification.nelsen11 θ hθ0 hθ1).IsNQD :=
  Verification.nelsen11_isNQD θ hθ0 hθ1

theorem nelsen11_pqd_iff (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (Verification.nelsen11 θ hθ0 hθ1).IsPQD ↔ θ = 0 :=
  Verification.nelsen11_isPQD_iff θ hθ0 hθ1

theorem nelsen11_ci_iff (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (Verification.nelsen11 θ hθ0 hθ1).IsCI ↔ θ = 0 :=
  Verification.nelsen11_isCI_iff θ hθ0 hθ1

theorem nelsen11_density_tp2_iff (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (Verification.nelsen11 θ hθ0 hθ1).HasMTP2Density ↔ θ = 0 :=
  Verification.nelsen11_density_tp2_iff θ hθ0 hθ1

theorem nelsen11_tails (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (Verification.nelsen11 θ hθ0 hθ1).HasLowerTailDependence 0 ∧
      (Verification.nelsen11 θ hθ0 hθ1).HasUpperTailDependence 0 :=
  Verification.nelsen11_tails θ hθ0 hθ1

theorem nelsen11_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ0 : ∀ z, 0 ≤ θ z) (hθ1 : ∀ z, θ z ≤ 1/2)
    (hlim : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun z => (Verification.nelsen11 (θ z) (hθ0 z) (hθ1 z)).cdf ![u,v]) l
      (𝓝 ((Copula.independence 2).cdf ![u,v])) := by
  simpa [Copula.cdf_independence, Fin.prod_univ_two] using
    Verification.nelsen11_tendsto_zero θ hθ0 hθ1 hlim u v

theorem nelsen11_cd (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (Verification.nelsen11 θ hθ0 hθ1).IsCD :=
  Verification.nelsen11_isCD θ hθ0 hθ1

theorem nelsen11_lowerOrthant_antitone {θ η : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/2) (hθη : θ ≤ η) :
    (Verification.nelsen11 η hη0 hη1).LowerOrthantLE (Verification.nelsen11 θ hθ0 hθ1) :=
  Verification.nelsen11_lowerOrthant_antitone hθ0 hθ1 hη0 hη1 hθη

theorem nelsen11_schur_monotone {θ η : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/2) (hθη : θ ≤ η) :
    (Verification.nelsen11 θ hθ0 hθ1).SchurBothLE (Verification.nelsen11 η hη0 hη1) :=
  Verification.nelsen11_schur_monotone hθ0 hθ1 hη0 hη1 hθη

end Papers.AnsariRockel2024
