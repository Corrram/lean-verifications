import Papers.AnsariRockel2026XiRho.BandDensitySections
import Verification.CubeFubini

/-! # Propositions 2 and 4(ii): absolute continuity and an MTP2 density -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

theorem sourceBandDensity_integrable {b : ℝ} (hb : 0 < b) : Integrable (sourceBandDensity b) := by
  have hi := ((Copula.independence 2).measurePreserving_eval 1).integrable_comp_of_integrable
    (sourceBandHeight_integrable hb)
  change Integrable (fun x : Fin 2 → I => sourceBandHeight b (x 1)) at hi
  refine hi.mono' (sourceBandDensity_measurable hb).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sourceBandDensity_nonneg hb x)]
    exact sourceBandDensity_le_height hb x

/-- Integrating the density over every lower orthant gives the original source CDF. -/
theorem sourceBandDensity_cdf {b : ℝ} (hb : 0 < b) (u : Fin 2 → I) :
    (∫ x in Iic u, sourceBandDensity b x) = (sourceBand b hb).cdf u := by
  have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
  rw [← he, integral_cube_Iic_iterated (sourceBandDensity_integrable hb)]
  simp_rw [sourceBandDensity_section hb]
  exact (sourceBand_cdf b hb _ _).symm

/-- This is an equality of probability measures, not a pointwise candidate density. -/
theorem sourceBand_toMeasure_density (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).toMeasure =
      (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (sourceBandDensity b x)) :=
  Copula.toMeasure_eq_withDensity_of_cdf_integral _ (sourceBandDensity_integrable hb)
    (sourceBandDensity_nonneg hb) (sourceBandDensity_cdf hb)

/-- Proposition 2: the entire positive source family is absolutely continuous. -/
theorem sourceBand_absolutelyContinuous (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).toMeasure ≪ (volume : Measure (Fin 2 → I)) := by
  rw [sourceBand_toMeasure_density]
  exact withDensity_absolutelyContinuous _ _

/-- The support's increasing interval endpoints imply total positivity of the density. -/
theorem sourceBandDensity_isMTP2 {b : ℝ} (hb : 0 < b) : IsMTP2 (sourceBandDensity b) := by
  rw [Copula.isMTP2_fin_two_iff]
  intro u w v z huw hvz
  change sourceBandDensity b ![u,z] * sourceBandDensity b ![w,v] ≤
    sourceBandDensity b ![u,v] * sourceBandDensity b ![w,z]
  have hval (s t : I) (h : b*(s : ℝ) < sourceBandIntercept b t ∧
      sourceBandIntercept b t ≤ b*(s : ℝ)+1) :
      sourceBandDensity b ![s,t] = sourceBandHeight b t := ite_eq_left h
  have hA := sourceBandIntercept_monotone hb hvz
  have hB := mul_le_mul_of_nonneg_left (show (u : ℝ) ≤ w from huw) hb.le
  by_cases huz : b*(u : ℝ) < sourceBandIntercept b z ∧ sourceBandIntercept b z ≤ b*(u : ℝ)+1
  · by_cases hwv : b*(w : ℝ) < sourceBandIntercept b v ∧ sourceBandIntercept b v ≤ b*(w : ℝ)+1
    · have huv : b*(u : ℝ) < sourceBandIntercept b v ∧ sourceBandIntercept b v ≤ b*(u : ℝ)+1 :=
        ⟨lt_of_le_of_lt hB hwv.1, hA.trans huz.2⟩
      have hwz : b*(w : ℝ) < sourceBandIntercept b z ∧ sourceBandIntercept b z ≤ b*(w : ℝ)+1 :=
        ⟨hwv.1.trans_le hA, huz.2.trans (by linarith)⟩
      rw [hval u z huz, hval w v hwv, hval u v huv, hval w z hwz]
      exact le_of_eq (mul_comm _ _)
    · have hz : sourceBandDensity b ![w,v] = 0 := ite_eq_right hwv
      rw [hz, mul_zero]
      exact mul_nonneg (sourceBandDensity_nonneg hb _) (sourceBandDensity_nonneg hb _)
  · have hz : sourceBandDensity b ![u,z] = 0 := ite_eq_right huz
    rw [hz, zero_mul]
    exact mul_nonneg (sourceBandDensity_nonneg hb _) (sourceBandDensity_nonneg hb _)

/-- Proposition 4(ii), with an actual nonnegative measurable Lebesgue density. -/
theorem sourceBand_hasMTP2Density (b : ℝ) (hb : 0 < b) : (sourceBand b hb).HasMTP2Density :=
  ⟨sourceBandDensity b, sourceBandDensity_measurable hb, sourceBandDensity_nonneg hb,
    sourceBandDensity_isMTP2 hb, sourceBand_toMeasure_density b hb⟩

end Papers.AnsariRockel2026XiRho
