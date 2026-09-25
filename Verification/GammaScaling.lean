import Verification.GammaPowerLaplace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem gammaPDF_scale {a b c x : ℝ} (hb : 0<b) (hc : 0<c) (hx : 0<x) :
    ENNReal.ofReal c*gammaPDF a (b/c) (c*x)=gammaPDF a b x := by
  rw [gammaPDF_of_nonneg (by positivity),gammaPDF_of_nonneg hx.le,
    ← ENNReal.ofReal_mul hc.le]
  congr 1
  rw [Real.div_rpow hb.le hc.le,Real.mul_rpow hc.le hx.le,
    Real.rpow_sub hc,Real.rpow_one]
  have he : b/c*(c*x)=b*x := by field_simp
  rw [he]
  have hp := (Real.rpow_pos_of_pos hc a).ne'
  field_simp

theorem gammaMeasure_map_mul {a b c : ℝ} (hb : 0<b) (hc : 0<c) :
    (gammaMeasure a b).map (fun x => c*x)=gammaMeasure a (b/c) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hm : Measurable (fun x : ℝ => c*x) := by fun_prop
  have hg (d : ℝ) : Measurable (gammaPDF a d) := (measurable_gammaPDFReal a d).ennreal_ofReal
  have hfm : Measurable (fun x : ℝ => f (c*x)) := hf.comp hm
  rw [lintegral_map hf hm,gammaMeasure,gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul _ (hg b) hfm,
    lintegral_withDensity_eq_lintegral_mul _ (hg (b/c)) hf]
  simp only [Pi.mul_apply]
  have hgf : Measurable (fun x => gammaPDF a (b/c) x*f x) := (hg (b/c)).mul hf
  conv_rhs => rw [← Real.smul_map_volume_mul_left hc.ne']
  rw [lintegral_smul_measure,lintegral_map hgf hm,
    smul_eq_mul,abs_of_pos hc,← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with x hx
  rcases lt_or_gt_of_ne hx with hn|hp
  · simp only [gammaPDF_of_neg hn,gammaPDF_of_neg (mul_neg_of_pos_of_neg hc hn),
      zero_mul,mul_zero]
  · rw [← mul_assoc,gammaPDF_scale hb hc hp]

end Verification
