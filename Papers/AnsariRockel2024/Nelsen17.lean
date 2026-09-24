import Verification.Nelsen17Conditional
import Verification.Nelsen17Tails

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

theorem nelsen17_isCI (θ : ℝ) (hθ : θ ≠ 0) (hθ1 : -1 ≤ θ) :
    (Verification.nelsen17 θ hθ).IsCI :=
  Verification.nelsen17_isCI θ hθ hθ1

theorem nelsen17_isCD (θ : ℝ) (hθ : θ ≠ 0) (hθ1 : θ ≤ -1) :
    (Verification.nelsen17 θ hθ).IsCD :=
  Verification.nelsen17_isCD θ hθ hθ1

theorem nelsen17_tails (θ : ℝ) (hθ : θ ≠ 0) :
    (Verification.nelsen17 θ hθ).HasLowerTailDependence 0 ∧
      (Verification.nelsen17 θ hθ).HasUpperTailDependence 0 :=
  Verification.nelsen17_tails θ hθ

end Papers.AnsariRockel2024
