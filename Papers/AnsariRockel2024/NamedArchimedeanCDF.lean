import Copula.Families.Joe
import Copula.Families.Nelsen

/-! # Joe source CDF on the closed square -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Table 1's Joe CDF, with grounded zero-axis values made explicit. -/
theorem joe_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.joe θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        1 - (((1 - (u : ℝ)) ^ θ + (1 - (v : ℝ)) ^ θ) -
          (1 - (u : ℝ)) ^ θ * (1 - (v : ℝ)) ^ θ) ^ θ⁻¹ := by
  by_cases hu : u = 0
  · subst u
    simpa using (Copula.joe θ hθ).cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    simpa [hu] using (Copula.joe θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  rw [Copula.cdf_joe θ hθ ![u, v] hp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ite_false]
  congr 1
  ring_nf

/-- Table 2's independence endpoint for Joe. -/
theorem joe_one : Copula.joe 1 le_rfl = Copula.independence 2 := Copula.joe_one


/-- Promote an analytic positive-coordinate CDF formula to the closed square. -/
private theorem closedSquareCDF_of_positive (C : Copula 2) (F : I → I → ℝ)
    (h : ∀ u v : I, u ≠ 0 → v ≠ 0 → C.cdf ![u, v] = F u v)
    (u v : I) :
    C.cdf ![u, v] = if u = 0 ∨ v = 0 then 0 else F u v := by
  by_cases hu : u = 0
  · subst u
    simpa using C.cdf_eq_zero_of_coord_eq_zero ![0, v] 0 rfl
  by_cases hv : v = 0
  · subst v
    simpa [hu] using C.cdf_eq_zero_of_coord_eq_zero ![u, 0] 1 rfl
  simpa [hu, hv] using h u v hu hv

/-- Table 1's Nelsen 2 CDF on the closed square. -/
theorem nelsen2_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.nelsen2 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        max 0 (1 - (((1 - (u : ℝ)) ^ θ + (1 - (v : ℝ)) ^ θ) ^ θ⁻¹)) := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using Copula.cdf_nelsen2 θ hθ ![a, b] hp

/-- Table 1's Genest–Ghoudi (Nelsen 15) CDF on the closed square. -/
theorem genestGhoudi_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.genestGhoudi θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (max 0 (1 - (((1 - (u : ℝ) ^ θ⁻¹) ^ θ +
          (1 - (v : ℝ) ^ θ⁻¹) ^ θ) ^ θ⁻¹))) ^ θ := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using Copula.cdf_genestGhoudi θ hθ ![a, b] hp

/-- Table 1's Nelsen 12 CDF on the closed square. -/
theorem nelsen12_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.nelsen12 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (1 + (((u : ℝ)⁻¹ - 1) ^ θ + ((v : ℝ)⁻¹ - 1) ^ θ) ^ θ⁻¹)⁻¹ := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using Copula.cdf_nelsen12 θ hθ ![a, b] hp

/-- Table 1's Nelsen 14 CDF on the closed square. -/
theorem nelsen14_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.nelsen14 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (1 + (((u : ℝ) ^ (-θ⁻¹) - 1) ^ θ +
          ((v : ℝ) ^ (-θ⁻¹) - 1) ^ θ) ^ θ⁻¹) ^ (-θ) := by
  apply closedSquareCDF_of_positive
  intro a b ha hb
  have hp : ∀ i : Fin 2, (![a, b] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using ha
    · simpa using hb
  simpa using Copula.cdf_nelsen14 θ hθ ![a, b] hp


/-- Table 2's lower Fréchet endpoint of Nelsen 2. -/
theorem nelsen2_one : Copula.nelsen2 1 le_rfl = Copula.countermonotonic :=
  Copula.nelsen2_one

/-- Table 2's lower Fréchet endpoint of Genest–Ghoudi. -/
theorem genestGhoudi_one : Copula.genestGhoudi 1 le_rfl = Copula.countermonotonic :=
  Copula.genestGhoudi_one

/-- Table 2's Clayton specialization of Nelsen 12. -/
theorem nelsen12_one :
    Copula.nelsen12 1 le_rfl = Copula.clayton 2 1 (by norm_num) := Copula.nelsen12_one

/-- Table 2's Clayton specialization of Nelsen 14. -/
theorem nelsen14_one :
    Copula.nelsen14 1 le_rfl = Copula.clayton 2 1 (by norm_num) := Copula.nelsen14_one

end Papers.AnsariRockel2024
