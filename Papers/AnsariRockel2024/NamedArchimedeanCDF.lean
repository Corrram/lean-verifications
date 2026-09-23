import Copula.Families.Joe

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

end Papers.AnsariRockel2024
