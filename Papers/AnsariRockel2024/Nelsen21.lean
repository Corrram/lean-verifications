import Verification.Nelsen21

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

end Papers.AnsariRockel2024
