import Verification.Nelsen10

/-! # Tables 1–3: Nelsen 10, its actual CDF, endpoints and dependence exclusions -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen10_cdf (θ u v : I) (hθ : 0 < (θ:ℝ)) :
    (Verification.nelsen10 θ).cdf ![u,v] =
      (u:ℝ)*v/(1+(1-(u:ℝ)^(θ:ℝ))*(1-(v:ℝ)^(θ:ℝ)))^(θ:ℝ)⁻¹ :=
  Verification.nelsen10_cdf θ u v hθ

theorem nelsen10_zero : Verification.nelsen10 0 = Copula.independence 2 :=
  Verification.nelsen10_zero

theorem nelsen10_one : Verification.nelsen10 1 = Copula.amh (-1) le_rfl (by norm_num) :=
  Verification.nelsen10_one

theorem nelsen10_nqd (θ : I) : (Verification.nelsen10 θ).IsNQD :=
  Verification.nelsen10_isNQD θ

theorem nelsen10_pqd_iff (θ : I) : (Verification.nelsen10 θ).IsPQD ↔ θ = 0 :=
  Verification.nelsen10_isPQD_iff θ

theorem nelsen10_ci_iff (θ : I) : (Verification.nelsen10 θ).IsCI ↔ θ = 0 :=
  Verification.nelsen10_isCI_iff θ

theorem nelsen10_density_tp2_iff (θ : I) :
    (Verification.nelsen10 θ).HasMTP2Density ↔ θ = 0 :=
  Verification.nelsen10_density_tp2_iff θ

theorem nelsen10_tails (θ : I) :
    (Verification.nelsen10 θ).HasLowerTailDependence 0 ∧
      (Verification.nelsen10 θ).HasUpperTailDependence 0 :=
  Verification.nelsen10_tails θ

end Papers.AnsariRockel2024
