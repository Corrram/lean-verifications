import Papers.AnsariRockel2024.ExtremeValueOrders
import Copula.Families.Gumbel

/-! # Full-square source CDF for the Gumbel–Hougaard family -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Table 1's Gumbel–Hougaard CDF on the whole closed square. The paper's
logarithmic expression applies to positive coordinates; copula groundedness
supplies the values on the two zero axes. -/
theorem gumbel_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.gumbel θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.exp (-(((-Real.log u) ^ θ + (-Real.log v) ^ θ) ^ θ⁻¹)) := by
  by_cases hu : u = 0
  · subst u
    simp
  by_cases hv : v = 0
  · subst v
    simp
  have hp : ∀ i : Fin 2, (![u, v] i) ≠ 0 := by
    intro i
    fin_cases i
    · simpa using hu
    · simpa using hv
  rw [Copula.cdf_gumbel θ hθ ![u, v] hp]
  simp [hu, hv]


/-- Table 1's Tawn CDF at positive coordinates, with all finite shape and
weight endpoints included. -/
theorem tawn_cdf_positive (θ : ℝ) (hθ : 1 ≤ θ) (α β u v : I)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (Copula.tawn θ hθ α β).cdf ![u, v] =
      (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) ^ (1 - (β : ℝ)) *
        Real.exp (-(((α : ℝ) * (-Real.log u)) ^ θ +
          ((β : ℝ) * (-Real.log v)) ^ θ) ^ θ⁻¹) := by
  have hup : (0 : ℝ) < u := lt_of_le_of_ne u.property.1
    (Ne.symm (fun h => hu (Subtype.ext h)))
  have hvp : (0 : ℝ) < v := lt_of_le_of_ne v.property.1
    (Ne.symm (fun h => hv (Subtype.ext h)))
  have hpow (i : Fin 2) :
      Copula.unitPower (![u, v] i) (![α, β] i) (![α, β] i).property.1 ≠ 0 := by
    intro he
    have hz := congrArg (fun x : I => (x : ℝ)) he
    fin_cases i
    · exact (Real.rpow_pos_of_pos hup _).ne' (by simpa using hz)
    · exact (Real.rpow_pos_of_pos hvp _).ne' (by simpa using hz)
  rw [Copula.tawn, Copula.cdf_maxProduct,
    Copula.cdf_gumbel θ hθ _ hpow, Copula.cdf_independence]
  simp only [Fin.prod_univ_two, Copula.coe_unitPower,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    unitInterval.coe_symm_eq, Real.log_rpow hup, Real.log_rpow hvp]
  have he1 : -((α : ℝ) * Real.log (u : ℝ)) =
      (α : ℝ) * (-Real.log u) := by ring
  have he2 : -((β : ℝ) * Real.log (v : ℝ)) =
      (β : ℝ) * (-Real.log v) := by ring
  rw [he1, he2]
  ring

/-- The Tawn formula on the closed square, making its zero-axis extension
explicit rather than applying `log 0` in the paper's analytic notation. -/
theorem tawn_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (α β u v : I) :
    (Copula.tawn θ hθ α β).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) ^ (1 - (β : ℝ)) *
          Real.exp (-(((α : ℝ) * (-Real.log u)) ^ θ +
            ((β : ℝ) * (-Real.log v)) ^ θ) ^ θ⁻¹) := by
  by_cases hu : u = 0
  · subst u
    simp
  by_cases hv : v = 0
  · subst v
    simp
  rw [tawn_cdf_positive θ hθ α β u v hu hv]
  simp [hu, hv]

end Papers.AnsariRockel2024
