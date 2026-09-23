import Copula.Families.Joe
import Copula.Families.Frank
import Copula.Families.FrankNegative
import Copula.Families.Nelsen
import Copula.Families.Nelsen8

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
  exact Copula.joe_cdf_full θ hθ u v

/-- Table 2's independence endpoint for Joe. -/
theorem joe_one : Copula.joe 1 le_rfl = Copula.independence 2 := Copula.joe_one


/-- Table 1's Frank CDF for the positive parameter branch, including grounded zero axes.
The negative branch and zero case are proved below. -/
theorem frank_positive_cdf_full (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (Copula.frank θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        -Real.log (1 - (1 - Real.exp (-θ * (u : ℝ))) *
          (1 - Real.exp (-θ * (v : ℝ))) / (1 - Real.exp (-θ))) / θ :=
  Copula.frank_cdf_full θ hθ u v

/-- The negative Frank branch as an exact reflected CDF on the closed square.
The printed logarithmic form is proved separately below. -/
theorem frank_negative_cdf_reflected (θ : ℝ) (hθ : θ < 0) (u v : I) :
    (Copula.frankNegative θ hθ).cdf ![u, v] =
      (u : ℝ) - (if u = 0 ∨ unitInterval.symm v = 0 then 0 else
        -Real.log (1 - (1 - Real.exp (θ * (u : ℝ))) *
          (1 - Real.exp (θ * (unitInterval.symm v : ℝ))) /
          (1 - Real.exp θ)) / (-θ)) :=
  Copula.frankNegative_cdf_full θ hθ u v

/-- Table 1's printed negative-parameter Frank CDF, including every boundary point. -/
theorem frank_negative_cdf_source (θ : ℝ) (hθ : θ < 0) (u v : I) :
    (Copula.frankNegative θ hθ).cdf ![u, v] =
      -Real.log (1 + (Real.exp (-θ * (u : ℝ)) - 1) *
        (Real.exp (-θ * (v : ℝ)) - 1) / (Real.exp (-θ) - 1)) / θ :=
  Copula.frankNegative_cdf_source θ hθ u v
/-- Table 1's Frank family at its zero parameter is independence. -/
theorem frank_zero_cdf (u v : I) :
    (Copula.independence 2).cdf ![u, v] = (u : ℝ) * (v : ℝ) := by
  simp only [Copula.cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]

/-- Table 1's Nelsen 2 CDF on the closed square. -/
theorem nelsen2_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.nelsen2 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        max 0 (1 - (((1 - (u : ℝ)) ^ θ + (1 - (v : ℝ)) ^ θ) ^ θ⁻¹)) := by
  exact Copula.nelsen2_cdf_full θ hθ u v

/-- Table 1's printed Nelsen 8 rational CDF on the entire closed square. -/
theorem nelsen8_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.nelsen8 θ hθ).cdf ![u, v] =
      max 0 ((θ ^ 2 * (u : ℝ) * (v : ℝ) -
        (1 - (u : ℝ)) * (1 - (v : ℝ))) /
        (θ ^ 2 - (θ - 1) ^ 2 * (1 - (u : ℝ)) * (1 - (v : ℝ)))) :=
  Copula.nelsen8_cdf_full θ hθ u v

/-- Table 1's Genest–Ghoudi (Nelsen 15) CDF on the closed square. -/
theorem genestGhoudi_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.genestGhoudi θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (max 0 (1 - (((1 - (u : ℝ) ^ θ⁻¹) ^ θ +
          (1 - (v : ℝ) ^ θ⁻¹) ^ θ) ^ θ⁻¹))) ^ θ := by
  exact Copula.genestGhoudi_cdf_full θ hθ u v

/-- Table 1's Nelsen 12 CDF on the closed square. -/
theorem nelsen12_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.nelsen12 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (1 + (((u : ℝ)⁻¹ - 1) ^ θ + ((v : ℝ)⁻¹ - 1) ^ θ) ^ θ⁻¹)⁻¹ := by
  exact Copula.nelsen12_cdf_full θ hθ u v

/-- Table 1's Nelsen 14 CDF on the closed square. -/
theorem nelsen14_cdf_full (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    (Copula.nelsen14 θ hθ).cdf ![u, v] =
      if u = 0 ∨ v = 0 then 0 else
        (1 + (((u : ℝ) ^ (-θ⁻¹) - 1) ^ θ +
          ((v : ℝ) ^ (-θ⁻¹) - 1) ^ θ) ^ θ⁻¹) ^ (-θ) := by
  exact Copula.nelsen14_cdf_full θ hθ u v

/-- Table 2's lower Fréchet endpoint of Nelsen 2. -/
theorem nelsen2_one : Copula.nelsen2 1 le_rfl = Copula.countermonotonic :=
  Copula.nelsen2_one

/-- Table 2's lower Fréchet endpoint of Nelsen 8. -/
theorem nelsen8_one : Copula.nelsen8 1 le_rfl = Copula.countermonotonic :=
  Copula.nelsen8_one

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
