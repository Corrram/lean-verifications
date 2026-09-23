import Papers.AnsariRockel2024.Definitions
import Copula.TailDependence.ExtremeValue
import Copula.TailDependence.Nelsen2
import Copula.TailDependence.Nelsen8
import Copula.TailDependence.Joe
import Copula.Order.FGMSchur
import Copula.Order.Frechet

/-! # Further Tables 3 and 5: tail limits and parameter orders

These statements connect the article's cells to the pinned library proofs.
Both tails include existence of the limit and all admitted finite parameters.
The Frechet order corrects the source's direction for the W weight.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem gumbel_tails (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.gumbel θ hθ).HasLowerTailDependence 0 ∧
      (Copula.gumbel θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  ⟨Copula.hasLowerTailDependence_gumbel θ hθ, Copula.hasUpperTailDependence_gumbel θ hθ⟩

/-- Table 3: Joe has its stated lower and upper tail coefficients. -/
theorem joe_tails (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.joe θ hθ).HasLowerTailDependence 0 ∧
      (Copula.joe θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  ⟨Copula.hasLowerTailDependence_joe θ hθ,
    Copula.hasUpperTailDependence_joe θ hθ⟩

/-- Table 3: Nelsen 8 has zero lower and upper tail coefficients. -/
theorem nelsen8_tails (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen8 θ hθ).HasLowerTailDependence 0 ∧
      (Copula.nelsen8 θ hθ).HasUpperTailDependence 0 :=
  ⟨Copula.hasLowerTailDependence_nelsen8 θ hθ,
    Copula.hasUpperTailDependence_nelsen8 θ hθ⟩

/-- Table 3: Nelsen 8 increases in lower-orthant order for θ ≥ 1. -/
theorem nelsen8_lowerOrthant {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η)
    (hθη : θ ≤ η) :
    (Copula.nelsen8 θ hθ).LowerOrthantLE (Copula.nelsen8 η hη) :=
  Copula.lowerOrthantLE_nelsen8 hθ hη hθη
/-- Table 3: Nelsen 2 has the stated lower and upper tail coefficients. -/
theorem nelsen2_tails (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen2 θ hθ).HasLowerTailDependence 0 ∧
      (Copula.nelsen2 θ hθ).HasUpperTailDependence (2 - (2 : ℝ) ^ θ⁻¹) :=
  ⟨Copula.hasLowerTailDependence_nelsen2 θ hθ,
    Copula.hasUpperTailDependence_nelsen2 θ hθ⟩
theorem marshallOlkin_tails (α β : I) :
    (Copula.marshallOlkin α β).HasLowerTailDependence (if α = 1 ∧ β = 1 then 1 else 0) ∧
      (Copula.marshallOlkin α β).HasUpperTailDependence (min (α : ℝ) (β : ℝ)) :=
  ⟨Copula.hasLowerTailDependence_marshallOlkin α β,
    Copula.hasUpperTailDependence_marshallOlkin α β⟩

theorem cuadrasAuge_tails (δ : I) :
    (Copula.cuadrasAuge δ).HasLowerTailDependence (if δ = 1 then 1 else 0) ∧
      (Copula.cuadrasAuge δ).HasUpperTailDependence (δ : ℝ) :=
  ⟨Copula.hasLowerTailDependence_cuadrasAuge δ, Copula.hasUpperTailDependence_cuadrasAuge δ⟩

theorem tawn_tails (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (Copula.tawn θ hθ α β).HasLowerTailDependence 0 ∧
      (Copula.tawn θ hθ α β).HasUpperTailDependence
        ((α : ℝ) + (β : ℝ) - ((α : ℝ) ^ θ + (β : ℝ) ^ θ) ^ θ⁻¹) :=
  ⟨Copula.hasLowerTailDependence_tawn θ hθ α β,
    Copula.hasUpperTailDependence_tawn θ hθ α β⟩

/-- Two-direction Schur comparison on the entire signed FGM parameter interval. -/
theorem fgm_schur_iff (θ η : ℝ) (hθ : |θ| ≤ 1) (hη : |η| ≤ 1) :
    (Copula.fgm θ hθ).SchurBothLE (Copula.fgm η hη) ↔ |θ| ≤ |η| :=
  Copula.schurBothLE_fgm_iff hθ hη

/-- Increasing M's weight and decreasing W's weight increases the copula in LO order. -/
theorem frechet_parameter_order (a b a' b' : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1)
    (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hab' : a' + b' ≤ 1)
    (haa : a ≤ a') (hbb : b' ≤ b) :
    (Copula.frechet a b ha hb hab).LowerOrthantLE (Copula.frechet a' b' ha' hb' hab') :=
  Copula.lowerOrthantLE_frechet ha hb hab ha' hb' hab' haa hbb

/-- The source's increasing-in-W-weight direction fails already at the endpoints. -/
theorem frechet_order_counterexample :
    ¬(Copula.frechet 0 0 (by norm_num) (by norm_num) (by norm_num)).LowerOrthantLE
      (Copula.frechet 0 1 (by norm_num) (by norm_num) (by norm_num)) := by
  intro h
  have ht := h ![Copula.unitHalf, Copula.unitHalf]
  norm_num [Copula.cdf_frechet, Copula.cdf_independence, Copula.cdf_countermonotonic,
    Fin.prod_univ_two, Copula.unitHalf] at ht

end Papers.AnsariRockel2024
