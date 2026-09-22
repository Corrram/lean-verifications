import Verification.IncreasingBandDensity
import Verification.ClampedRhoOptimization

/-! # CDF formulas for a standardized uniform band -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval ENNReal

namespace Verification.IncreasingBand

variable (B : IncreasingBand)

theorem density_row_prefix (u t : I) :
    (∫ v in Iic t, B.density (u,v)) = unitClamp (((t:ℝ)-B.lower u)/B.width) := by
  let a : I := ⟨B.lower u,B.lower_nonneg u,by linarith [B.lower_le u,B.width_pos]⟩
  let b : I := ⟨B.lower u+B.width,by linarith [B.lower_nonneg u,B.width_pos],by linarith [B.lower_le u]⟩
  have he : (fun v : I => B.density (u,v)) = (Icc a b).indicator (fun _ => 1/B.width) := by
    funext v
    simp only [density,indicator,mem_Icc]
    change (if a ≤ v ∧ v ≤ b then _ else _) = (if a ≤ v ∧ v ≤ b then _ else _)
    split_ifs <;> rfl
  have hs : Iic t ∩ Icc a b = Icc a (min t b) := by ext v; simp only [mem_inter_iff,mem_Iic,mem_Icc,le_min_iff]; tauto
  rw [he,setIntegral_indicator measurableSet_Icc,hs,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,unitInterval.volume_Icc,smul_eq_mul]
  have hm : ((min t b : I):ℝ) = min (t:ℝ) (B.lower u+B.width) := rfl
  rw [hm]
  change (ENNReal.ofReal (min (t:ℝ) (B.lower u+B.width)-B.lower u)).toReal * (1/B.width) = _
  by_cases ht : (t:ℝ) ≤ B.lower u
  · rw [min_eq_left (by linarith [B.width_pos]),ENNReal.ofReal_eq_zero.mpr (by linarith)]
    simp only [ENNReal.toReal_zero,zero_mul]
    unfold unitClamp
    rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) B.width_pos.le)]
    norm_num
  · have hta : B.lower u ≤ (t:ℝ) := le_of_not_ge ht
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (le_min hta (by linarith [B.width_pos])))]
    unfold unitClamp
    rw [max_eq_right (div_nonneg (sub_nonneg.mpr hta) B.width_pos.le)]
    by_cases htb : (t:ℝ) ≤ B.lower u+B.width
    · rw [min_eq_left htb,min_eq_right ((div_le_one B.width_pos).mpr (by linarith))]
      ring
    · rw [min_eq_right (le_of_not_ge htb),min_eq_left ((one_le_div B.width_pos).mpr (by linarith))]
      field_simp [B.width_pos.ne']
      ring

theorem measure_prefix (u t : I) :
    B.measure.real (Iic u ×ˢ Iic t) =
      ∫ s in Iic u, unitClamp (((t:ℝ)-B.lower s)/B.width) := by
  rw [measure,Measure.real,withDensity_apply _ (measurableSet_Iic.prod measurableSet_Iic),
    ← ofReal_integral_eq_lintegral_ofReal B.density_integrable.integrableOn
      (Eventually.of_forall fun p => (B.density_mem p).1),
    ENNReal.toReal_ofReal (integral_nonneg (fun p => (B.density_mem p).1))]
  change (∫ p in Iic u ×ˢ Iic t, B.density p ∂(volume : Measure I).prod volume) = _
  rw [← Measure.prod_restrict,integral_prod]
  · simp_rw [B.density_row_prefix]
  · rw [Measure.prod_restrict]
    exact B.density_integrable.integrableOn

theorem marginal_prefix (t : I) : B.marginal.real (Iic t) =
    ∫ s : I, unitClamp (((t:ℝ)-B.lower s)/B.width) := by
  have hp := B.measure_prefix 1 t
  have hs : Iic (1:I) = univ := by ext v; simp [unitInterval.le_one']
  rw [hs,Measure.restrict_univ] at hp
  rw [marginal,map_measureReal_apply measurable_snd measurableSet_Iic]
  convert hp using 1
  congr 1
  ext p
  simp

/-- Quantile inversion identifies the standardized CDF, including null flat fibers. -/
theorem copula_cdf (u v : I) : B.copula.cdf ![u,v] =
    ∫ s in Iic u, unitClamp ((((unitQuantile B.marginal v: I):ℝ)-B.lower s) / B.width) := by
  change (B.measure.map B.sample).real (Iic ![u,v]) = _
  rw [map_measureReal_apply B.sample_measurable measurableSet_Iic]
  have hae : ∀ᵐ p : I × I ∂B.measure,
      unitQuantile B.marginal (unitCDF B.marginal p.2) = p.2 :=
    ae_of_ae_map (f:=Prod.snd) measurable_snd.aemeasurable (quantile_unitCDF_ae B.marginal)
  have hm : Monotone (unitCDF B.marginal) := fun _ _ h => measureReal_mono (Iic_subset_Iic.mpr h)
  have he : B.sample ⁻¹' Iic ![u,v] =ᵐ[B.measure] Iic u ×ˢ Iic (unitQuantile B.marginal v) := by
    filter_upwards [hae] with p hp
    apply propext
    simp only [mem_preimage,mem_Iic,sample,Pi.le_def,Fin.forall_fin_two,
      Matrix.cons_val_zero,Matrix.cons_val_one,mem_prod]
    rw [← B.marginal_cdf]
    constructor
    · rintro ⟨hu,hv⟩
      exact ⟨hu,hp ▸ monotone_unitQuantile B.marginal hv⟩
    · rintro ⟨hu,hv⟩
      exact ⟨hu,by simpa only [unitCDF_quantile] using hm hv⟩
  have hh : B.measure.real (B.sample ⁻¹' Iic ![u,v]) =
      B.measure.real (Iic u ×ˢ Iic (unitQuantile B.marginal v)) :=
    congrArg ENNReal.toReal (measure_congr he)
  rw [hh,B.measure_prefix]

end Verification.IncreasingBand
