import Verification.Nelsen11

/-! # Tables 1–3: Nelsen 11 as an actual copula measure -/

open ProbabilityTheory
open scoped unitInterval

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

end Papers.AnsariRockel2024
