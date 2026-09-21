import Papers.AnsariRockel2024.Definitions
import Verification.FrechetDependence
import Copula.Order.Orthant

/-! # Tables 5 and A.4: Frechet and Mardia dependence classifications

The valid Frechet simplex is a,b>=0 and a+b<=1. Mardia has W weight
theta^2(1-theta)/2. Its independence parameter zero belongs to both CI and CD.
Density TP2 is interpreted literally as existence of a Lebesgue TP2 density;
positive singular weights rule out even absolute continuity.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem frechet_ci_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).IsCI ↔ b = 0 :=
  Verification.frechet_ci_iff a b ha hb hab

theorem frechet_cd_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).IsCD ↔ a = 0 :=
  Verification.frechet_cd_iff a b ha hb hab

theorem frechet_absolutelyContinuous_iff (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ a = 0 ∧ b = 0 :=
  Verification.frechet_absolutelyContinuous_iff a b ha hb hab

theorem frechet_density_tp2_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).HasMTP2Density ↔ a = 0 ∧ b = 0 :=
  Verification.frechet_density_tp2_iff a b ha hb hab

theorem mardia_ci_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).IsCI ↔ θ = 0 ∨ θ = 1 := by
  rw [Copula.mardia, frechet_ci_iff]
  constructor
  · intro h
    have he : θ ^ 2 * (1 - θ) = 0 := by linarith
    rcases mul_eq_zero.mp he with hz | hz
    · exact Or.inl (eq_zero_of_pow_eq_zero hz)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem mardia_cd_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).IsCD ↔ θ = 0 ∨ θ = -1 := by
  rw [Copula.mardia, frechet_cd_iff]
  constructor
  · intro h
    have he : θ ^ 2 * (1 + θ) = 0 := by linarith
    rcases mul_eq_zero.mp he with hz | hz
    · exact Or.inl (eq_zero_of_pow_eq_zero hz)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

private theorem mardia_weights_zero (θ : ℝ) :
    (θ ^ 2 * (1 + θ) / 2 = 0 ∧ θ ^ 2 * (1 - θ) / 2 = 0) ↔ θ = 0 := by
  constructor
  · rintro ⟨ha, hb⟩
    have he : θ ^ 2 = 0 := by nlinarith
    exact eq_zero_of_pow_eq_zero he
  · rintro rfl
    norm_num

theorem mardia_absolutelyContinuous_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ θ = 0 := by
  rw [Copula.mardia, frechet_absolutelyContinuous_iff, mardia_weights_zero]

theorem mardia_density_tp2_iff (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.mardia θ hθ).HasMTP2Density ↔ θ = 0 := by
  rw [Copula.mardia, frechet_density_tp2_iff, mardia_weights_zero]

/-- A concrete incomparable pair proves the source's lack of parameter ordering. -/
theorem mardia_not_lowerOrthant_ordered :
    ¬(Copula.mardia (1 / 2) (by norm_num)).LowerOrthantLE (Copula.mardia 0 (by norm_num)) ∧
      ¬(Copula.mardia 0 (by norm_num)).LowerOrthantLE (Copula.mardia (1 / 2) (by norm_num)) := by
  constructor
  · intro h
    have ht := h ![⟨1 / 8, by constructor <;> norm_num⟩, ⟨1 / 8, by constructor <;> norm_num⟩]
    simp only [Copula.mardia, Copula.cdf_frechet, Copula.cdf_comonotonic_two,
      Copula.cdf_countermonotonic, Copula.cdf_independence, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at ht
    norm_num at ht
  · intro h
    have ht := h ![⟨1 / 8, by constructor <;> norm_num⟩, ⟨7 / 8, by constructor <;> norm_num⟩]
    simp only [Copula.mardia, Copula.cdf_frechet, Copula.cdf_comonotonic_two,
      Copula.cdf_countermonotonic, Copula.cdf_independence, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] at ht
    norm_num at ht

end Papers.AnsariRockel2024
