import Verification.Nelsen21Tails

/-! # Nelsen 21: measure constructor, printed CDF, and countermonotonic endpoint -/

open ProbabilityTheory
open scoped unitInterval

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

end Papers.AnsariRockel2024
