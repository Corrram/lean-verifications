import Verification.Nelsen17

/-! # Tables 1–2: Nelsen 17 on both nonzero parameter branches -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen17_cdf_full (θ : ℝ) (hθ : θ ≠ 0) (u v : I) :
    (Verification.nelsen17 θ hθ).cdf ![u,v] =
      (1+(((1+(u:ℝ))^(-θ)-1)*((1+(v:ℝ))^(-θ)-1))/((2:ℝ)^(-θ)-1))^(-θ⁻¹)-1 :=
  Verification.nelsen17_cdf_full θ hθ u v

theorem nelsen17_neg_one : Verification.nelsen17 (-1) (by norm_num) = Copula.independence 2 :=
  Verification.nelsen17_neg_one

end Papers.AnsariRockel2024
