import Papers.AnsariRockel2026XiRho.BandSupport
import Papers.AnsariRockel2026XiRho.BandKendall

/-! # Every nonzero positive diagonal band is asymmetric -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- The support meets the vertical axis above zero but the horizontal axis only at zero. -/
theorem sourceBand_not_exchangeable (b : ℝ) (hb : 0 < b) :
    ¬ (sourceBand b hb).IsExchangeable := by
  intro he
  let f : I × I → Fin 2 → ℝ := fun p i => (bandSample b p (![1,0] i) : ℝ)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hm : ((sourceBand b hb).toMeasure.map (fun u i => (u i : ℝ))) =
      (volume : Measure (I × I)).map f := by
    conv_lhs => rw [← he]
    rw [Copula.transpose, Copula.toMeasure_reindex, sourceBand_sampling,
      Measure.map_map (by fun_prop) (continuous_bandSample b).measurable,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hs : f (0,1) ∈ bandSupport b := by
    rw [← sourceBand_support_set b hb, hm, support_map_uniform f hf]
    exact ⟨(0,1),rfl⟩
  let t : I := clampedMeanUnit b 1
  have ht : 0 < (t : ℝ) := by
    have h := clampedMean_strictMonoOn hb.le
      (show (0 : ℝ) ∈ Icc 0 (b+1) by constructor <;> linarith)
      (show (1 : ℝ) ∈ Icc 0 (b+1) by constructor <;> linarith) (by norm_num : (0 : ℝ) < 1)
    rw [clampedMean_zero b hb.le] at h
    exact h
  have hl : 0 < bandLowerEdge b t := by
    rw [bandLowerEdge_eq_mean hb]
    have h := clampedMean_strictMonoOn hb.le
      (show (0 : ℝ) ∈ Icc 0 (b+1) by constructor <;> linarith)
      (show b*(t : ℝ) ∈ Icc 0 (b+1) from
        ⟨mul_nonneg hb.le t.property.1, by nlinarith [t.property.2]⟩) (mul_pos hb ht)
    rwa [clampedMean_zero b hb.le] at h
  have hx := hs.2.1
  change bandLowerEdge b (clampedMean b (b*(0 : ℝ)+1)) ≤ 0 at hx
  norm_num only [mul_zero, zero_add] at hx
  exact (not_le_of_gt hl) hx

/-- The reflected negative branch is asymmetric as well. -/
theorem negativeSourceBand_not_exchangeable (b : ℝ) (hb : 0 < b) :
    ¬ (negativeSourceBand b hb).IsExchangeable := by
  intro he
  apply sourceBand_not_exchangeable b hb
  apply Copula.reflect_injective {1}
  change (sourceBand b hb).transpose.reflect {1} = (sourceBand b hb).reflect {1}
  rw [← Copula.transpose_reflect_first]
  change (negativeSourceBand b hb).transpose = (sourceBand b hb).reflect {1}
  rw [he, negativeSourceBand_eq_response_reflection]

end Papers.AnsariRockel2026XiRho
