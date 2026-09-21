import Papers.OrendayLaresRockel2026TauFootruleBeta.JointGeometry
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Section 5: section areas, their unique maximum, and volume -/

open MeasureTheory ProbabilityTheory Set

namespace Papers.OrendayLaresRockel2026TauFootruleBeta

noncomputable def lowerFootrule (b : ℝ) : ℝ := 3 / 16 * (1 + b) ^ 2 - 1 / 2
noncomputable def upperFootrule (b : ℝ) : ℝ := 1 - 3 / 8 * (1 - b) ^ 2
noncomputable def sectionArea (b : ℝ) : ℝ := 3 / 256 * (3 - b) ^ 2 * (1 + b) * (5 - 3 * b)

theorem footrule_limits (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    lowerFootrule b ≤ upperFootrule b ∧ upperFootrule b ≤ 1 := by
  have h := mul_nonneg (by linarith [hb.1] : 0 ≤ 1 + b) (by linarith [hb.2] : 0 ≤ 5 - 3 * b)
  unfold lowerFootrule upperFootrule
  constructor <;> nlinarith [sq_nonneg (1 - b)]

theorem sectionArea_nonneg (b : ℝ) (hb : b ∈ Icc (-1) 1) : 0 ≤ sectionArea b := by
  unfold sectionArea
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (by linarith [hb.1])) (by linarith [hb.2])

theorem sectionArea_integral (b : ℝ) :
    (∫ p in lowerFootrule b..upperFootrule b, 2 / 3 * (1 - p)) = sectionArea b := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := lowerFootrule b) (b := upperFootrule b)
    (f := fun p : ℝ => 2 / 3 * p - p ^ 2 / 3)
    (f' := fun p => 2 / 3 * (1 - p)) (fun p _ => by
      convert! ((hasDerivAt_id p).const_mul (2 / 3)).sub
        (((hasDerivAt_id p).pow 2).div_const 3) using 1; dsimp; ring)
    ((show Continuous (fun p : ℝ => 2 / 3 * (1 - p)) by fun_prop).intervalIntegrable _ _)
  rw [h]
  unfold lowerFootrule upperFootrule sectionArea
  ring

private theorem fibre_volume (p b : ℝ) :
    volume ((fun t : ℝ => (t, p, b)) ⁻¹' jointRegion) =
      if b ∈ Icc (-1) 1 ∧ p ∈ Icc (lowerFootrule b) (upperFootrule b)
      then ENNReal.ofReal (2 / 3 * (1 - p)) else 0 := by
  classical
  by_cases h : b ∈ Icc (-1) 1 ∧ p ∈ Icc (lowerFootrule b) (upperFootrule b)
  · rw [ite_eq_left h]
    have he : (fun t : ℝ => (t, p, b)) ⁻¹' jointRegion =
        Icc (4 / 3 * p - 1 / 3) (2 / 3 * p + 1 / 3) := by
      ext t
      simp only [mem_preimage, mem_jointRegion, mem_Icc]
      exact ⟨fun ht => ht.2.2.2, fun ht => ⟨h.1, h.2.1, h.2.2, ht⟩⟩
    rw [he, Real.volume_Icc]
    congr 1
    ring
  · rw [ite_eq_right h]
    have he : (fun t : ℝ => (t, p, b)) ⁻¹' jointRegion = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro t ht
      rw [mem_preimage, mem_jointRegion] at ht
      exact h ⟨ht.1, ht.2.1, ht.2.2.1⟩
    rw [he, measure_empty]

theorem fixed_beta_section_area (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    volume {z : ℝ × ℝ | (z.1, z.2, b) ∈ jointRegion} = ENNReal.ofReal (sectionArea b) := by
  have hm : MeasurableSet {z : ℝ × ℝ | (z.1, z.2, b) ∈ jointRegion} :=
    jointRegion_closed.measurableSet.preimage (by fun_prop)
  change (volume.prod volume) {z : ℝ × ℝ | (z.1, z.2, b) ∈ jointRegion} = _
  rw [Measure.prod_apply_symm hm]
  have he (p : ℝ) : volume ((fun t : ℝ => (t, p)) ⁻¹'
      {z : ℝ × ℝ | (z.1, z.2, b) ∈ jointRegion}) =
      (Icc (lowerFootrule b) (upperFootrule b)).indicator
        (fun p => ENNReal.ofReal (2 / 3 * (1 - p))) p := by
    change volume ((fun t : ℝ => (t, p, b)) ⁻¹' jointRegion) = _
    rw [fibre_volume]
    simp [hb, indicator_apply]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Icc]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (footrule_limits b hb).1, sectionArea_integral]
  · exact (show Continuous (fun p : ℝ => 2 / 3 * (1 - p)) by fun_prop).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with p hp
    change 0 ≤ 2 / 3 * (1 - p)
    linarith [hp.2, (footrule_limits b hb).2]

theorem sectionArea_integral_total : (∫ b in (-1 : ℝ)..1, sectionArea b) = 31 / 40 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1)
    (f := fun b : ℝ => 3 / 256 * (45 * b - 6 * b ^ 2 - 34 / 3 * b ^ 3 + 5 * b ^ 4 - 3 / 5 * b ^ 5))
    (f' := sectionArea) (fun b _ => by
      convert! ((((((hasDerivAt_id b).const_mul 45).sub
        (((hasDerivAt_id b).pow 2).const_mul 6)).sub
        (((hasDerivAt_id b).pow 3).const_mul (34 / 3))).add
        (((hasDerivAt_id b).pow 4).const_mul 5)).sub
        (((hasDerivAt_id b).pow 5).const_mul (3 / 5))).const_mul (3 / 256) using 1
      unfold sectionArea
      dsimp
      ring)
    ((show Continuous sectionArea by unfold sectionArea; fun_prop).intervalIntegrable _ _)
  rw [h]
  norm_num

theorem sectionArea_derivative (b : ℝ) :
    HasDerivAt sectionArea (3 / 64 * (3 - b) * (3 * (b - 1) ^ 2 - 4)) b := by
  unfold sectionArea
  convert! (((((hasDerivAt_id b).const_sub 3).pow 2).const_mul (3 / 256)).mul
    ((hasDerivAt_id b).const_add 1)).mul
    (((hasDerivAt_id b).const_mul 3).const_sub 5) using 1; dsimp; ring

theorem sectionArea_maximum (b : ℝ) (hb : b ∈ Icc (-1) 1) :
    sectionArea b ≤ 1 / 4 + Real.sqrt 3 / 6 ∧
      (sectionArea b = 1 / 4 + Real.sqrt 3 / 6 ↔ b = 1 - 2 / Real.sqrt 3) := by
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hrpos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hdiv : 2 / Real.sqrt 3 = 2 * Real.sqrt 3 / 3 := by
    apply (div_eq_iff (ne_of_gt hrpos)).mpr
    nlinarith
  have hQ : 0 < 9 * b ^ 2 - (42 + 12 * Real.sqrt 3) * b + 45 + 44 * Real.sqrt 3 := by
    nlinarith [sq_nonneg b, mul_nonneg (by linarith : 0 ≤ 42 + 12 * Real.sqrt 3)
      (by linarith [hb.2] : 0 ≤ 1 - b)]
  have hid : 1 / 4 + Real.sqrt 3 / 6 - sectionArea b =
      (b - (1 - 2 * Real.sqrt 3 / 3)) ^ 2 *
        (9 * b ^ 2 - (42 + 12 * Real.sqrt 3) * b + 45 + 44 * Real.sqrt 3) / 256 := by
    unfold sectionArea
    have hr3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, hr]
    ring_nf
    rw [hr, hr3]
    ring
  have hn := mul_nonneg (sq_nonneg (b - (1 - 2 * Real.sqrt 3 / 3))) hQ.le
  constructor
  · nlinarith
  · rw [hdiv]
    constructor
    · intro he
      have hz : (b - (1 - 2 * Real.sqrt 3 / 3)) ^ 2 = 0 := by nlinarith
      nlinarith [sq_nonneg (b - (1 - 2 * Real.sqrt 3 / 3))]
    · intro he
      rw [he, sub_self, zero_pow (by decide), zero_mul, zero_div] at hid
      rw [he]
      linarith

theorem jointRegion_volume : volume jointRegion = ENNReal.ofReal (31 / 40 : ℝ) := by
  classical
  let R : Set ((ℝ × ℝ) × ℝ) := MeasurableEquiv.prodAssoc ⁻¹' jointRegion
  have hm : MeasurableSet R := jointRegion_closed.measurableSet.preimage
    MeasurableEquiv.prodAssoc.measurable
  have hR : volume R = volume jointRegion :=
    volume_preserving_prodAssoc.measure_preimage jointRegion_closed.measurableSet.nullMeasurableSet
  rw [← hR]
  change (volume.prod volume) R = _
  rw [Measure.prod_apply_symm hm]
  have hsec (b : ℝ) : volume ((fun z : ℝ × ℝ => (z, b)) ⁻¹' R) =
      (Icc (-1 : ℝ) 1).indicator (fun b => ENNReal.ofReal (sectionArea b)) b := by
    by_cases hb : b ∈ Icc (-1) 1
    · rw [indicator_of_mem hb]
      exact fixed_beta_section_area b hb
    · rw [indicator_of_notMem hb]
      have he : (fun z : ℝ × ℝ => (z, b)) ⁻¹' R = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro ⟨t, p⟩ ht
        change (t, p, b) ∈ jointRegion at ht
        exact hb ((mem_jointRegion t p b).mp ht).1
      rw [he, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      sectionArea_integral_total]
  · exact (show Continuous sectionArea by unfold sectionArea; fun_prop).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with b hb
    exact sectionArea_nonneg b hb

theorem sectionArea_maximum_attained :
    1 - 2 / Real.sqrt 3 ∈ Icc (-1 : ℝ) 1 ∧
      sectionArea (1 - 2 / Real.sqrt 3) = 1 / 4 + Real.sqrt 3 / 6 := by
  have hr0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hd0 : 0 ≤ 2 / Real.sqrt 3 := div_nonneg (by norm_num) hr0.le
  have hd2 : 2 / Real.sqrt 3 ≤ 2 := (div_le_iff₀ hr0).mpr (by nlinarith)
  have hb : 1 - 2 / Real.sqrt 3 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  exact ⟨hb, (sectionArea_maximum _ hb).2.mpr rfl⟩

end Papers.OrendayLaresRockel2026TauFootruleBeta
