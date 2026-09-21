import Verification.ConditionalMean

/-! # The universal correlation-ratio bound eta <= 2 xi -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem square_integral_le {f : I → ℝ} (hi : Integrable f)
    (hs : Integrable (fun u => f u ^ 2)) : (∫ u : I, f u) ^ 2 ≤ ∫ u : I, f u ^ 2 := by
  let m := ∫ u : I, f u
  have he : (fun u : I => (f u - m) ^ 2) = fun u => f u ^ 2 - (2 * m) * f u + m ^ 2 := by
    funext u; ring
  have hpos : 0 ≤ ∫ u : I, (f u - m) ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [he] at hpos
  have h₁ := integral_add (hs.sub (hi.const_mul (2 * m))) (integrable_const (m ^ 2))
  have h₂ := integral_sub hs (hi.const_mul (2 * m))
  simp only [Pi.sub_apply] at h₁ h₂
  rw [h₁, h₂, integral_const_mul] at hpos
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hpos
  dsimp [m] at hpos
  nlinarith only [hpos]

private theorem centered_measurable (C : Copula 2) :
    Measurable (fun p : I × I => C.conditionalCDF p.2 p.1 - (p.1 : ℝ)) :=
  C.measurable_conditionalCDF.sub (measurable_subtype_coe.comp measurable_fst)

private theorem centered_abs_le (C : Copula 2) (u t : I) :
    |C.conditionalCDF t u - (u : ℝ)| ≤ 1 := by
  apply abs_le.mpr
  constructor <;> linarith [C.conditionalCDF_nonneg t u, C.conditionalCDF_le_one t u,
    u.property.1, u.property.2]

private theorem centered_sq_integrable (C : Copula 2) :
    Integrable (fun p : I × I => (C.conditionalCDF p.2 p.1 - (p.1 : ℝ)) ^ 2)
      ((volume : Measure I).prod volume) := by
  refine (integrable_const (1 : ℝ)).mono' ((centered_measurable C).pow_const 2).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := centered_abs_le C p.1 p.2
    nlinarith [sq_abs (C.conditionalCDF p.2 p.1 - (p.1 : ℝ)), abs_nonneg (C.conditionalCDF p.2 p.1 - (p.1 : ℝ))]

private theorem centered_section (C : Copula 2) (t : I) :
    Integrable (fun u : I => C.conditionalCDF t u - (u : ℝ)) ∧
    Integrable (fun u : I => (C.conditionalCDF t u - (u : ℝ)) ^ 2) := by
  have hm := (centered_measurable C).comp (show Measurable (fun u : I => (u, t)) by fun_prop)
  constructor
  · refine (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun u => by
      simpa only [Real.norm_eq_abs] using centered_abs_le C u t
  · refine (integrable_const (1 : ℝ)).mono' (hm.pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := centered_abs_le C u t
      nlinarith [sq_abs (C.conditionalCDF t u - (u : ℝ)), abs_nonneg (C.conditionalCDF t u - (u : ℝ))]

private theorem centered_mean (C : Copula 2) (t : I) :
    (∫ u : I, C.conditionalCDF t u - (u : ℝ)) = 1 / 2 - conditionalMean C t := by
  have hi : Integrable (fun u : I => C.conditionalCDF t u) := by
    have h := (centered_section C t).1.add (Copula.integrable_continuous_unit volume continuous_subtype_val)
    change Integrable (fun u : I => C.conditionalCDF t u - (u : ℝ) + (u : ℝ)) at h
    simpa only [sub_add_cancel] using h
  rw [integral_sub hi (Copula.integrable_continuous_unit volume continuous_subtype_val), Copula.integral_unit_id]
  rw [conditionalMean_eq]
  ring

/-- Cauchy--Schwarz in the response threshold, averaged over the predictor rank. -/
theorem correlationRatio_le_twice_xi (C : Copula 2) :
    correlationRatio C ≤ 2 * C.chatterjeeXi := by
  have hb (t : I) : (conditionalMean C t - 1 / 2) ^ 2 ≤
      ∫ u : I, (C.conditionalCDF t u - (u : ℝ)) ^ 2 := by
    have h := square_integral_le (centered_section C t).1 (centered_section C t).2
    rw [centered_mean] at h
    nlinarith only [h]
  have hm : Measurable (fun t : I => conditionalMean C t) := by
    simp_rw [conditionalMean_eq]
    exact measurable_const.sub C.measurable_conditionalCDF.stronglyMeasurable.integral_prod_left.measurable
  have hi : Integrable (fun t : I => (conditionalMean C t - 1 / 2) ^ 2) := by
    refine (centered_sq_integrable C).integral_prod_right.mono'
      ((hm.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (conditionalMean C t - 1 / 2))] using hb t
  have h := integral_mono hi (centered_sq_integrable C).integral_prod_right hb
  rw [← integral_integral_swap (centered_sq_integrable C)] at h
  rw [correlationRatio, C.chatterjeeXi_eq_integral_centered_sq]
  linarith only [h]

private theorem centered_square_identity {f : I → ℝ} (hi : Integrable f)
    (hs : Integrable (fun u => f u ^ 2)) :
    (∫ u : I, (f u - ∫ v : I, f v) ^ 2) = (∫ u : I, f u ^ 2) - (∫ u : I, f u) ^ 2 := by
  let m := ∫ u : I, f u
  have he : (fun u : I => (f u - m) ^ 2) = fun u => f u ^ 2 - (2 * m) * f u + m ^ 2 := by
    funext u; ring
  change (∫ u : I, (f u - m) ^ 2) = _
  rw [he]
  have h₁ := integral_add (hs.sub (hi.const_mul (2 * m))) (integrable_const (m ^ 2))
  have h₂ := integral_sub hs (hi.const_mul (2 * m))
  simp only [Pi.sub_apply] at h₁ h₂
  rw [h₁, h₂, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  dsimp [m]
  ring

private theorem constant_centered_cdf_zero (C : Copula 2) (t : I) {c : ℝ}
    (h : ∀ᵐ u : I, C.conditionalCDF t u - (u : ℝ) = c) : c = 0 := by
  have hlow : ∀ᵐ u : I, -(u : ℝ) ≤ c := by
    filter_upwards [h] with u hu
    linarith [C.conditionalCDF_nonneg t u]
  have hupp : ∀ᵐ u : I, c ≤ 1 - (u : ℝ) := by
    filter_upwards [h] with u hu
    linarith [C.conditionalCDF_le_one t u]
  have lower : 0 ≤ c := by
    by_contra hh
    have hc : c < 0 := lt_of_not_ge hh
    let v : I := ⟨min (1 / 2) (-c / 2), le_min (by norm_num) (by linarith),
      (min_le_left _ _).trans (by norm_num)⟩
    have hv : 0 < (v : ℝ) := lt_min (by norm_num) (by linarith)
    have hvol : (volume : Measure I) (Iic v) ≠ 0 := by
      rw [unitInterval.volume_Iic]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hv)
    obtain ⟨u, hu, hb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol (ae_restrict_of_ae hlow)
    have huv : (u : ℝ) ≤ v := hu
    have hvv : (v : ℝ) ≤ -c / 2 := min_le_right _ _
    linarith
  have upper : c ≤ 0 := by
    by_contra hh
    have hc : 0 < c := lt_of_not_ge hh
    let v : I := ⟨1 - min (1 / 2) (c / 2), by linarith [min_le_left (1 / 2 : ℝ) (c / 2)],
      by have h := le_min (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : 0 ≤ c / 2); linarith⟩
    have hv : 0 < 1 - (v : ℝ) := by
      dsimp [v]
      have h := lt_min (by norm_num : (0 : ℝ) < 1 / 2) (by linarith : 0 < c / 2)
      linarith
    have hvol : (volume : Measure I) (Ici v) ≠ 0 := by
      rw [unitInterval.volume_Ici]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr hv)
    obtain ⟨u, hu, hb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hvol (ae_restrict_of_ae hupp)
    have huv : (v : ℝ) ≤ u := hu
    have hvv : 1 - (v : ℝ) ≤ c / 2 := by dsimp [v]; linarith [min_le_right (1 / 2 : ℝ) (c / 2)]
    linarith
  exact le_antisymm upper lower

/-- Equality in eta <= 2 xi is possible only at independence's coefficient pair (0,0). -/
theorem correlationRatio_eq_twice_xi_iff (C : Copula 2) :
    correlationRatio C = 2 * C.chatterjeeXi ↔ C.chatterjeeXi = 0 := by
  constructor
  · intro heq
    let g (t u : I) := C.conditionalCDF t u - (u : ℝ)
    let m (t : I) := ∫ u : I, g t u
    have hm : Measurable m := (centered_measurable C).stronglyMeasurable.integral_prod_left.measurable
    have hsq : Integrable (fun t => m t ^ 2) := by
      refine (centered_sq_integrable C).integral_prod_right.mono'
        (hm.pow_const 2).aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (m t))]
        exact square_integral_le (centered_section C t).1 (centered_section C t).2
    have hdef (t : I) : (∫ u : I, (g t u - m t) ^ 2) = (∫ u : I, g t u ^ 2) - m t ^ 2 :=
      centered_square_identity (centered_section C t).1 (centered_section C t).2
    have hi : Integrable (fun t : I => ∫ u : I, (g t u - m t) ^ 2) := by
      simp_rw [hdef]
      exact (centered_sq_integrable C).integral_prod_right.sub hsq
    have hz : (∫ t : I, ∫ u : I, (g t u - m t) ^ 2) = 0 := by
      simp_rw [hdef]
      rw [integral_sub (centered_sq_integrable C).integral_prod_right hsq,
        ← integral_integral_swap (centered_sq_integrable C)]
      have hm' : (fun t : I => m t ^ 2) = fun t => (conditionalMean C t - 1 / 2) ^ 2 := by
        funext t
        dsimp [m, g]
        rw [centered_mean]
        ring
      rw [hm']
      rw [correlationRatio, C.chatterjeeXi_eq_integral_centered_sq] at heq
      dsimp [g]
      linarith only [heq]
    have ha := (integral_eq_zero_iff_of_nonneg (fun t => integral_nonneg fun _ => sq_nonneg _) hi).mp hz
    have hg : ∀ᵐ t : I, ∀ᵐ u : I, g t u = 0 := by
      filter_upwards [ha] with t ht
      have hit : Integrable (fun u : I => (g t u - m t) ^ 2) := by
        have he : (fun u : I => (g t u - m t) ^ 2) =
            fun u => g t u ^ 2 - (2 * m t) * g t u + m t ^ 2 := by funext u; ring
        rw [he]
        exact ((centered_section C t).2.sub ((centered_section C t).1.const_mul _)).add (integrable_const _)
      have hu := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hit).mp ht
      have hc : ∀ᵐ u : I, g t u = m t := by
        filter_upwards [hu] with u hu
        exact sub_eq_zero.mp (sq_eq_zero_iff.mp hu)
      have hm0 := constant_centered_cdf_zero C t hc
      simpa only [hm0] using hc
    rw [C.chatterjeeXi_eq_integral_centered_sq, integral_integral_swap (centered_sq_integrable C)]
    have hz' : (∫ t : I, ∫ u : I, g t u ^ 2) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hg] with t ht
      apply integral_eq_zero_of_ae
      filter_upwards [ht] with u hu
      simp [hu]
    change 6 * (∫ t : I, ∫ u : I, g t u ^ 2) = 0
    rw [hz', mul_zero]
  · intro h
    have hu := correlationRatio_le_twice_xi C
    have hl := correlationRatio_nonneg C
    rw [h] at hu ⊢
    linarith

end Verification
