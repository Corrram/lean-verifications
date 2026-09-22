import Papers.AnsariRockel2026XiRho.BandDensityPrimitive
import Verification.BandMeanInverse
import Verification.TruncatedPrimitive

/-! # Identifying every conditional section of the band density -/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

theorem sourceBandIntercept_mem {b : ℝ} (hb : 0 < b) (v : I) :
    sourceBandIntercept b v ∈ Icc (0 : ℝ) (b+1) := by
  have hz : sourceBandIntercept b 0 = 0 := by
    simp [sourceBandIntercept, (bandCut_mem hb).1]
  have ho : sourceBandIntercept b 1 = b+1 := by
    have hp : 0 < bandCut b := lt_min (by positivity) (by positivity)
    simp [sourceBandIntercept, show ¬(1 : ℝ) ≤ bandCut b by linarith [(bandCut_mem hb).2],
      show ¬(1 : ℝ) ≤ 1-bandCut b by linarith]
  have h₁ := sourceBandIntercept_monotone hb (show (0 : I) ≤ v from v.property.1)
  have h₂ := sourceBandIntercept_monotone hb (show v ≤ (1 : I) from v.property.2)
  rw [hz] at h₁
  rw [ho] at h₂
  exact ⟨h₁,h₂⟩

theorem sourceBandIntercept_eq_normalized {b : ℝ} (hb : 0 < b) (v : I) :
    sourceBandIntercept b v = bandIntercept b hb.le v := by
  apply (clampedMean_strictMonoOn hb.le).injOn (sourceBandIntercept_mem hb v) (bandIntercept_mem _ _ _)
  rw [sourceBandIntercept_mean hb, bandIntercept_mean]

theorem sourceBandIntercept_strictMono {b : ℝ} (hb : 0 < b) : StrictMono (sourceBandIntercept b) := by
  intro v w hvw
  apply lt_of_le_of_ne (sourceBandIntercept_monotone hb hvw.le)
  intro he
  have hh := congrArg (clampedMean b) he
  rw [sourceBandIntercept_mean hb, sourceBandIntercept_mean hb] at hh
  exact (ne_of_lt hvw) (Subtype.ext hh)

/-- A density version including the upper band edge; its value on that null edge is immaterial. -/
noncomputable def sourceBandDensity (b : ℝ) (x : Fin 2 → I) : ℝ :=
  if b*(x 0 : ℝ) < sourceBandIntercept b (x 1) ∧
    sourceBandIntercept b (x 1) ≤ b*(x 0 : ℝ)+1 then sourceBandHeight b (x 1) else 0

theorem sourceBandDensity_nonneg {b : ℝ} (hb : 0 < b) (x : Fin 2 → I) :
    0 ≤ sourceBandDensity b x := by
  unfold sourceBandDensity
  split_ifs
  · exact sourceBandHeight_nonneg hb _
  · rfl

theorem sourceBandDensity_le_height {b : ℝ} (hb : 0 < b) (x : Fin 2 → I) :
    sourceBandDensity b x ≤ sourceBandHeight b (x 1) := by
  unfold sourceBandDensity
  split_ifs
  · rfl
  · exact sourceBandHeight_nonneg hb _

theorem sourceBandDensity_measurable {b : ℝ} (hb : 0 < b) : Measurable (sourceBandDensity b) := by
  have ha := (sourceBandIntercept_monotone hb).measurable
  have hw : Measurable (sourceBandHeight b) := by
    unfold sourceBandHeight sqrtSlope
    apply Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const) (by fun_prop)
    exact Measurable.ite (measurableSet_le measurable_subtype_coe measurable_const)
      measurable_const (by fun_prop)
  unfold sourceBandDensity
  apply Measurable.ite
  · exact (measurableSet_lt (by fun_prop) (ha.comp (measurable_pi_apply 1))).inter
      (measurableSet_le (ha.comp (measurable_pi_apply 1)) (by fun_prop))
  · exact hw.comp (measurable_pi_apply 1)
  · exact measurable_const

/-- Integrating the density in the response rank gives exactly the source conditional CDF. -/
theorem sourceBandDensity_section {b : ℝ} (hb : 0 < b) (u v : I) :
    (∫ t in Iic v, sourceBandDensity b ![u,t]) =
      unitClamp (sourceBandIntercept b v-b*(u : ℝ)) := by
  let l := clampedMeanUnit b (b*(u : ℝ))
  let r := clampedMeanUnit b (b*(u : ℝ)+1)
  have hbu : b*(u : ℝ) ∈ Icc (0 : ℝ) (b+1) :=
    ⟨mul_nonneg hb.le u.property.1, by nlinarith [u.property.2]⟩
  have hbu1 : b*(u : ℝ)+1 ∈ Icc (0 : ℝ) (b+1) :=
    ⟨by nlinarith [u.property.1], by nlinarith [u.property.2]⟩
  have hlr : l ≤ r := clampedMean_monotone b (by linarith)
  have hl : sourceBandIntercept b l = b*(u : ℝ) := by
    rw [sourceBandIntercept_eq_normalized hb]
    exact bandIntercept_clampedMean b hb.le hbu
  have hr : sourceBandIntercept b r = b*(u : ℝ)+1 := by
    rw [sourceBandIntercept_eq_normalized hb]
    exact bandIntercept_clampedMean b hb.le hbu1
  have he : (fun t : I => sourceBandDensity b ![u,t]) = (Ioc l r).indicator (sourceBandHeight b) := by
    funext t
    have hiff : (b*(u : ℝ) < sourceBandIntercept b t ∧ sourceBandIntercept b t ≤ b*(u : ℝ)+1) ↔
        l < t ∧ t ≤ r := by
      rw [← hr, ← hl, (sourceBandIntercept_strictMono hb).lt_iff_lt,
        (sourceBandIntercept_strictMono hb).le_iff_le]
    simp only [sourceBandDensity, Matrix.cons_val_zero, Matrix.cons_val_one,
      Set.indicator, mem_Ioc, hiff]
  rw [he]
  exact integral_truncated_primitive (sourceBandHeight_integrable hb)
    (sourceBandIntercept_monotone hb) (sourceBandHeight_primitive hb) l r hlr _ hl hr v

end Papers.AnsariRockel2026XiRho
