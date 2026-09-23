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


/-- Both zero Tawn weights give independence, for every admissible shape. -/
theorem tawn_zero_zero (θ : ℝ) (hθ : 1 ≤ θ) :
    Copula.tawn θ hθ 0 0 = Copula.independence 2 := by
  have hw : (![ (0 : I), (0 : I)] : Fin 2 → I) = fun _ => 0 := by
    funext i
    fin_cases i <;> rfl
  simp [Copula.tawn, hw]

/-- Both unit Tawn weights recover the Gumbel–Hougaard copula. -/
theorem tawn_one_one (θ : ℝ) (hθ : 1 ≤ θ) :
    Copula.tawn θ hθ 1 1 = Copula.gumbel θ hθ := by
  have hw : (![ (1 : I), (1 : I)] : Fin 2 → I) = fun _ => 1 := by
    funext i
    fin_cases i <;> rfl
  simp [Copula.tawn, hw]

private theorem power_complement (u a : I) :
    (Copula.unitPower u a a.property.1 : ℝ) *
      (Copula.unitPower u (unitInterval.symm a) (unitInterval.symm a).property.1 : ℝ) =
        (u : ℝ) := by
  change (u : ℝ) ^ (a : ℝ) * (u : ℝ) ^ (1 - (a : ℝ)) = (u : ℝ)
  by_cases hu : (u : ℝ) = 0
  · by_cases ha : (a : ℝ) = 0
    · simp [hu, ha]
    · simp [hu, Real.zero_rpow ha]
  · rw [← Real.rpow_add (lt_of_le_of_ne u.property.1 (Ne.symm hu)),
      add_sub_cancel, Real.rpow_one]

theorem tawn_zero_left (θ : ℝ) (hθ : 1 ≤ θ) (β : I) :
    Copula.tawn θ hθ 0 β = Copula.independence 2 := by
  apply Copula.ext_cdf
  intro u
  rw [Copula.tawn, Copula.cdf_maxProduct]
  have hvec : (fun i : Fin 2 =>
      Copula.unitPower (u i) (![ (0 : I), β] i) (![ (0 : I), β] i).property.1) =
      Function.update (fun _ : Fin 2 => (1 : I)) 1
        (Copula.unitPower (u 1) β β.property.1) := by
    funext i
    fin_cases i <;> simp
  rw [hvec, (Copula.gumbel θ hθ).cdf_update_one]
  rw [Copula.cdf_independence, Copula.cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [unitInterval.symm_zero]
  simp only [Copula.coe_unitPower, unitInterval.coe_symm_eq]
  have hcoe : ((1 : I) : ℝ) = (1 : ℝ) := rfl
  rw [hcoe, Real.rpow_one]
  have hp : (u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ)) = (u 1 : ℝ) := by
    simpa only [Copula.coe_unitPower, unitInterval.coe_symm_eq] using
      power_complement (u 1) β
  calc
    _ = (u 0 : ℝ) * ((u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ))) := by ring
    _ = _ := by rw [hp]


theorem tawn_zero_right (θ : ℝ) (hθ : 1 ≤ θ) (α : I) :
    Copula.tawn θ hθ α 0 = Copula.independence 2 := by
  apply Copula.ext_cdf
  intro u
  rw [Copula.tawn, Copula.cdf_maxProduct]
  have hvec : (fun i : Fin 2 =>
      Copula.unitPower (u i) (![ α, (0 : I)] i) (![ α, (0 : I)] i).property.1) =
      Function.update (fun _ : Fin 2 => (1 : I)) 0
        (Copula.unitPower (u 0) α α.property.1) := by
    funext i
    fin_cases i <;> simp
  rw [hvec, (Copula.gumbel θ hθ).cdf_update_one]
  rw [Copula.cdf_independence, Copula.cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [unitInterval.symm_zero]
  simp only [Copula.coe_unitPower, unitInterval.coe_symm_eq]
  have hcoe : ((1 : I) : ℝ) = (1 : ℝ) := rfl
  rw [hcoe, Real.rpow_one]
  have hp : (u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ)) = (u 0 : ℝ) := by
    simpa only [Copula.coe_unitPower, unitInterval.coe_symm_eq] using
      power_complement (u 0) α
  calc
    _ = ((u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ))) * (u 1 : ℝ) := by ring
    _ = _ := by rw [hp]


theorem tawn_shape_one (α β : I) :
    Copula.tawn 1 le_rfl α β = Copula.independence 2 := by
  apply Copula.ext_cdf
  intro u
  rw [Copula.tawn, Copula.gumbel_one, Copula.cdf_maxProduct,
    Copula.cdf_independence, Copula.cdf_independence, Copula.cdf_independence]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Copula.coe_unitPower, unitInterval.coe_symm_eq]
  have h0 : (u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ)) = (u 0 : ℝ) := by
    simpa only [Copula.coe_unitPower, unitInterval.coe_symm_eq] using
      power_complement (u 0) α
  have h1 : (u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ)) = (u 1 : ℝ) := by
    simpa only [Copula.coe_unitPower, unitInterval.coe_symm_eq] using
      power_complement (u 1) β
  calc
    _ = ((u 0 : ℝ) ^ (α : ℝ) * (u 0 : ℝ) ^ (1 - (α : ℝ))) *
        ((u 1 : ℝ) ^ (β : ℝ) * (u 1 : ℝ) ^ (1 - (β : ℝ))) := by ring
    _ = _ := by rw [h0, h1]


end Papers.AnsariRockel2024
