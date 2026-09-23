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
  exact Copula.gumbel_cdf_full θ hθ u v

/-- Table 2's independence endpoint for Gumbel–Hougaard. -/
theorem gumbel_one : Copula.gumbel 1 le_rfl = Copula.independence 2 :=
  Copula.gumbel_one

/-- Table 1's Tawn CDF at positive coordinates, with all finite shape and
weight endpoints included. -/
theorem tawn_cdf_positive (θ : ℝ) (hθ : 1 ≤ θ) (α β u v : I)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (Copula.tawn θ hθ α β).cdf ![u, v] =
      (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) ^ (1 - (β : ℝ)) *
        Real.exp (-(((α : ℝ) * (-Real.log u)) ^ θ +
          ((β : ℝ) * (-Real.log v)) ^ θ) ^ θ⁻¹) := by
  exact Copula.tawn_cdf_positive θ hθ α β u v hu hv

/-- The Tawn formula on the closed square, making its zero-axis extension
explicit rather than applying `log 0` in the paper's analytic notation. -/
theorem tawn_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (α β u v : I) :
    (Copula.tawn θ hθ α β).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (u : ℝ) ^ (1 - (α : ℝ)) * (v : ℝ) ^ (1 - (β : ℝ)) *
          Real.exp (-(((α : ℝ) * (-Real.log u)) ^ θ +
            ((β : ℝ) * (-Real.log v)) ^ θ) ^ θ⁻¹) := by
  exact Copula.tawn_cdf_full θ hθ α β u v

/-- Both zero Tawn weights give independence, for every admissible shape. -/
theorem tawn_zero_zero (θ : ℝ) (hθ : 1 ≤ θ) :
    Copula.tawn θ hθ 0 0 = Copula.independence 2 := by
  exact Copula.tawn_zero_zero θ hθ

/-- Both unit Tawn weights recover the Gumbel–Hougaard copula. -/
theorem tawn_one_one (θ : ℝ) (hθ : 1 ≤ θ) :
    Copula.tawn θ hθ 1 1 = Copula.gumbel θ hθ := by
  exact Copula.tawn_one_one θ hθ

theorem tawn_zero_left (θ : ℝ) (hθ : 1 ≤ θ) (β : I) :
    Copula.tawn θ hθ 0 β = Copula.independence 2 := by
  exact Copula.tawn_zero_left θ hθ β

theorem tawn_zero_right (θ : ℝ) (hθ : 1 ≤ θ) (α : I) :
    Copula.tawn θ hθ α 0 = Copula.independence 2 := by
  exact Copula.tawn_zero_right θ hθ α

theorem tawn_shape_one (α β : I) :
    Copula.tawn 1 le_rfl α β = Copula.independence 2 := by
  exact Copula.tawn_shape_one α β

end Papers.AnsariRockel2024
