import Verification.Nelsen22Tails

/-! # Nelsen 22: trigonometric copula, exact CI/TP2 classification and tails -/

open ProbabilityTheory Set
open scoped unitInterval

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

end Papers.AnsariRockel2024
