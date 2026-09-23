import Papers.AnsariRockel2024.Nelsen7Results
import Verification.IntegralHinge
import Verification.LinearRationalIntegral
import Copula.Rank.Region.XiRho.Support.StochasticRho

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.AnsariRockel2024

private theorem nelsen7_height_nonneg (θ v : I) :
    0 ≤ (θ : ℝ) * v + 1 - θ := by
  nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]

private theorem nelsen7_height_mul_threshold (θ v : I) :
    ((θ : ℝ) * v + 1 - θ) * (Copula.nelsen7Threshold θ v : ℝ) =
      (1 - (θ : ℝ)) * (1 - (v : ℝ)) := by
  by_cases hz : (θ : ℝ) * v + 1 - θ = 0
  · have ht : (θ : ℝ) = 1 := by
      nlinarith [θ.property.2, mul_nonneg θ.property.1 v.property.1]
    rw [hz, ht]
    ring
  · dsimp [Copula.nelsen7Threshold]
    field_simp

private theorem nelsen7_height_times_remaining (θ v : I) :
    ((θ : ℝ) * v + 1 - θ) * (1 - (Copula.nelsen7Threshold θ v : ℝ)) =
      (v : ℝ) := by
  have ht := nelsen7_height_mul_threshold θ v
  nlinarith

private theorem nelsen7_cdf_hinge (θ u v : I) :
    (Copula.nelsen7 θ).cdf ![u, v] =
      max 0 (((θ : ℝ) * v + 1 - θ) * ((u : ℝ) -
        (Copula.nelsen7Threshold θ v : ℝ))) := by
  rw [Copula.cdf_nelsen7]
  congr 1
  have ht := nelsen7_height_mul_threshold θ v
  nlinarith

/-- The inner CDF integral in the paper's Spearman-rho calculation,
valid also at the countermonotonic and independence endpoints. -/
theorem nelsen7_integral_cdf_first (θ v : I) :
    (∫ u : I, (Copula.nelsen7 θ).cdf ![u, v]) =
      (v : ℝ) ^ 2 / (2 * ((θ : ℝ) * v + 1 - θ)) := by
  simp_rw [nelsen7_cdf_hinge θ]
  rw [Verification.integral_unit_linear_hinge _ (nelsen7_height_nonneg θ v)]
  let h : ℝ := (θ : ℝ) * v + 1 - θ
  let q : ℝ := 1 - (Copula.nelsen7Threshold θ v : ℝ)
  have hq : h * q = (v : ℝ) := nelsen7_height_times_remaining θ v
  change h * q ^ 2 / 2 = (v : ℝ) ^ 2 / (2 * h)
  by_cases hz : h = 0
  · have hv : (v : ℝ) = 0 := by rw [hz] at hq; simpa using hq.symm
    simp [hz, hv]
  · field_simp
    rw [← hq]
    ring

/-- Appendix A.5.1's one-variable rho integral, including both endpoints;
its logarithmic evaluation remains a separate calculus step. -/
theorem nelsen7_rho_integral (θ : I) :
    (Copula.nelsen7 θ).spearmanRho =
      12 * (∫ v : I, (v : ℝ) ^ 2 / (2 * ((θ : ℝ) * v + 1 - θ))) - 3 := by
  rw [Copula.RankRegion.XiRho.Support.spearmanRho_eq_iterated_cdf]
  simp_rw [nelsen7_integral_cdf_first θ]

/-- Appendix A.5.1's closed Spearman-rho expression at interior parameters. -/
theorem nelsen7_rho_interior (θ : I) (h0 : (0 : ℝ) < θ) (h1 : (θ : ℝ) < 1) :
    (Copula.nelsen7 θ).spearmanRho =
      12 * ((3 * (θ : ℝ) ^ 2 - 2 * θ -
        2 * ((θ : ℝ) - 1) ^ 2 * Real.log (1 - (θ : ℝ))) /
        (4 * (θ : ℝ) ^ 3)) - 3 := by
  rw [nelsen7_rho_integral,
    Verification.integral_unit_nelsen7_rational (θ : ℝ) h0 h1]

/-- Table 6's exact Nelsen 7 Spearman-rho formula on the full parameter
interval, with the two singular logarithmic endpoints stated separately. -/
theorem nelsen7_rho (θ : I) :
    (Copula.nelsen7 θ).spearmanRho =
      if θ = 0 then -1 else if θ = 1 then 0 else
        12 * ((3 * (θ : ℝ) ^ 2 - 2 * θ -
          2 * ((θ : ℝ) - 1) ^ 2 * Real.log (1 - (θ : ℝ))) /
          (4 * (θ : ℝ) ^ 3)) - 3 := by
  by_cases h0 : θ = 0
  · subst θ
    simp
  by_cases h1 : θ = 1
  · subst θ
    simp
  have hp : (0 : ℝ) < θ :=
    lt_of_le_of_ne θ.property.1 (Ne.symm (fun hz => h0 (Subtype.ext hz)))
  have hlt : (θ : ℝ) < 1 :=
    lt_of_le_of_ne θ.property.2 (fun hz => h1 (Subtype.ext hz))
  simpa [h0, h1] using nelsen7_rho_interior θ hp hlt

end Papers.AnsariRockel2024
