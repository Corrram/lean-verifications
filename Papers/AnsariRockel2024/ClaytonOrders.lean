import Verification.ClaytonOrder

/-! # Table 3: Clayton parameter orders on the full signed range

`Verification.claytonSigned θ` is the positive Clayton copula for `θ>0`, independence at
`θ=0` and the truncated negative branch for `-1≤θ<0`.
-/

open ProbabilityTheory Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem clayton_signed_positive {θ : ℝ} (h : 0 < θ) :
    Verification.claytonSigned θ = clayton 2 θ h := Verification.claytonSigned_pos h

theorem clayton_signed_zero : Verification.claytonSigned 0 = independence 2 :=
  Verification.claytonSigned_zero

theorem clayton_signed_negative {θ : ℝ} (hθ : -1 ≤ θ) (hn : θ < 0) :
    Verification.claytonSigned θ = claytonNegative θ hθ hn := Verification.claytonSigned_neg hθ hn

/-- Table 3: lower-orthant order increases with `θ` on all of `[-1,∞)`. -/
theorem clayton_lowerOrthant_mono {θ η : ℝ} (hθ : -1 ≤ θ) (hθη : θ ≤ η) :
    (Verification.claytonSigned θ).LowerOrthantLE (Verification.claytonSigned η) :=
  Verification.claytonSigned_lowerOrthant_mono hθ hθη

/-- Table 3: both-direction Schur order increases with `θ` on `θ≥0`. -/
theorem clayton_schur_nonnegative {θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ ≤ η) :
    (Verification.claytonSigned θ).SchurBothLE (Verification.claytonSigned η) :=
  Verification.claytonSigned_schur_nonnegative hθ hθη

/-- Table 3: both-direction Schur order decreases with `θ` on `-1≤θ≤0`. -/
theorem clayton_schur_nonpositive {θ η : ℝ} (hθ : -1 ≤ θ) (hθη : θ ≤ η) (hη : η ≤ 0) :
    (Verification.claytonSigned η).SchurBothLE (Verification.claytonSigned θ) :=
  Verification.claytonSigned_schur_nonpositive hθ hθη hη

/-- Table 2: negative parameters tending to zero give independence, pointwise on the square. -/
theorem clayton_negative_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, -1 ≤ θ a) (hn : ∀ a, θ a < 0) (hlim : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (claytonNegative (θ a) (hθ a) (hn a)).cdf ![u, v]) l
      (𝓝 ((u : ℝ) * v)) :=
  Verification.claytonNegative_tendsto_zero θ hθ hn hlim u v

end Papers.AnsariRockel2024
