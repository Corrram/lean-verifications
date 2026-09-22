import Papers.AnsariRockel2026XiRho.SourceBand
import Verification.SqrtSlopeIntegrals

/-! # The source density height integrates to its explicit intercept -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

noncomputable def sourceBandHeight (b : ℝ) (v : I) : ℝ :=
  if (v : ℝ) ≤ bandCut b then sqrtSlope b v
  else if (v : ℝ) ≤ 1-bandCut b then max b 1
  else sqrtSlope b (1-(v : ℝ))

theorem sourceBandHeight_nonneg {b : ℝ} (hb : 0 < b) (v : I) : 0 ≤ sourceBandHeight b v := by
  unfold sourceBandHeight
  split_ifs
  · exact sqrtSlope_nonneg hb.le _
  · exact hb.le.trans (le_max_left _ _)
  · exact sqrtSlope_nonneg hb.le _

theorem sourceBandHeight_integrable {b : ℝ} (hb : 0 < b) : Integrable (sourceBandHeight b) := by
  classical
  have h₁ : MeasurableSet {v : I | (v : ℝ) ≤ bandCut b} := measurableSet_le measurable_subtype_coe measurable_const
  have h₂ : MeasurableSet {v : I | (v : ℝ) ≤ 1-bandCut b} := measurableSet_le measurable_subtype_coe measurable_const
  exact Integrable.piecewise h₁ (sqrtSlope_integrable hb).integrableOn
    (Integrable.piecewise h₂ (integrable_const (max b 1)).integrableOn
      (sqrtSlope_reflection_integrable hb).integrableOn).integrableOn

private theorem height_low {b : ℝ} (hb : 0 < b) (v : I) (hv : (v : ℝ) ≤ bandCut b) :
    (∫ t in Iic v, sourceBandHeight b t) = Real.sqrt (2*b*(v : ℝ)) := by
  rw [← integral_sqrtSlope_Iic hb v]
  apply setIntegral_congr_fun measurableSet_Iic
  intro t ht
  exact ite_eq_left (show (t : ℝ) ≤ bandCut b from le_trans ht hv)

private theorem cut_sqrt {b : ℝ} (hb : 0 < b) :
    Real.sqrt (2*b*bandCut b) = min b 1 := by
  by_cases h : b ≤ 1
  · rw [bandCut_small hb h, min_eq_left h]
    convert Real.sqrt_sq hb.le using 2
    ring
  · rw [bandCut_large hb (by linarith), min_eq_right (by linarith)]
    have he : 2*b*(1/(2*b)) = 1 := by field_simp
    rw [he, Real.sqrt_one]

private theorem cut_middle {b : ℝ} (hb : 0 < b) :
    max b 1 * bandCut b = min b 1 / 2 := by
  by_cases h : b ≤ 1
  · rw [bandCut_small hb h, min_eq_left h, max_eq_right h]; ring
  · rw [bandCut_large hb (by linarith), min_eq_right (by linarith), max_eq_left (by linarith)]
    field_simp

private theorem height_mid {b : ℝ} (hb : 0 < b) (v : I)
    (hv0 : bandCut b ≤ (v : ℝ)) (hv1 : (v : ℝ) ≤ 1-bandCut b) :
    (∫ t in Iic v, sourceBandHeight b t) = min b 1+max b 1*((v : ℝ)-bandCut b) := by
  let c : I := ⟨bandCut b, (bandCut_mem hb).1, by linarith [(bandCut_mem hb).2]⟩
  have he := Copula.integral_Iic_add_Ioc_unit (sourceBandHeight_integrable hb) (show c ≤ v from hv0)
  have ht : (∫ t in Ioc c v, sourceBandHeight b t) = max b 1*((v : ℝ)-bandCut b) := by
    calc
      _ = ∫ _t in Ioc c v, max b 1 := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        rw [sourceBandHeight, ite_eq_right (by exact not_le_of_gt ht.1),
          ite_eq_left (show (t : ℝ) ≤ 1-bandCut b from le_trans ht.2 hv1)]
      _ = _ := by
        simp only [setIntegral_const, Measure.real, unitInterval.volume_Ioc, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by change 0 ≤ (v : ℝ)-bandCut b; linarith)]
        change ((v : ℝ)-bandCut b)*max b 1 = _
        ring
  rw [height_low hb c le_rfl, ht] at he
  change Real.sqrt (2*b*bandCut b)+max b 1*((v : ℝ)-bandCut b) = _ at he
  rw [cut_sqrt hb] at he
  exact he.symm

/-- Integrating the proposed density height recovers the source intercept at every threshold. -/
theorem sourceBandHeight_primitive {b : ℝ} (hb : 0 < b) (v : I) :
    (∫ t in Iic v, sourceBandHeight b t) = sourceBandIntercept b v := by
  by_cases h₁ : (v : ℝ) ≤ bandCut b
  · rw [height_low hb v h₁, sourceBandIntercept, ite_eq_left h₁]
  by_cases h₂ : (v : ℝ) ≤ 1-bandCut b
  · rw [height_mid hb v (by linarith) h₂, sourceBandIntercept, ite_eq_right h₁, ite_eq_left h₂]
    have hc := cut_middle hb
    by_cases h : b ≤ 1
    · rw [ite_eq_left h, min_eq_left h, max_eq_right h] at *
      nlinarith only [hc]
    · rw [ite_eq_right h, min_eq_right (by linarith : 1 ≤ b), max_eq_left (by linarith : 1 ≤ b)] at *
      nlinarith only [hc]
  · let d : I := ⟨1-bandCut b, by linarith [(bandCut_mem hb).2], by linarith [(bandCut_mem hb).1]⟩
    have hcd : bandCut b ≤ (d : ℝ) := by dsimp [d]; linarith [(bandCut_mem hb).2]
    have he := Copula.integral_Iic_add_Ioc_unit (sourceBandHeight_integrable hb) (show d ≤ v from le_of_not_ge h₂)
    have ht : (∫ t in Ioc d v, sourceBandHeight b t) =
        Real.sqrt (2*b*bandCut b)-Real.sqrt (2*b*(1-(v : ℝ))) := by
      calc
        _ = ∫ t in Ioc d v, sqrtSlope b (1-(t : ℝ)) := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro t ht
          have htd : 1-bandCut b < (t : ℝ) := ht.1
          rw [sourceBandHeight, ite_eq_right (by linarith [hcd]), ite_eq_right (by linarith)]
        _ = _ := by
          rw [integral_sqrtSlope_reflection_Ioc hb d v (le_of_not_ge h₂)]
          congr 3
          dsimp [d]; ring
    rw [height_mid hb d hcd le_rfl, ht, cut_sqrt hb] at he
    rw [sourceBandIntercept, ite_eq_right h₁, ite_eq_right h₂]
    have hc := cut_middle hb
    have hsum : min b 1+max b 1 = b+1 := min_add_max _ _
    change min b 1+max b 1*(1-bandCut b-bandCut b)+
      (min b 1-Real.sqrt (2*b*(1-(v : ℝ)))) = _ at he
    nlinarith only [he,hc,hsum]

end Papers.AnsariRockel2026XiRho
