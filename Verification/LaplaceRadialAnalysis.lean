import Verification.LaplaceJointDensity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem laplace_radial_integrand_bound {q t : ℝ} (hq : 0<q) (ht : 0<t) :
    t⁻¹*Real.exp (-t-q/(2*t))≤(2/q)*Real.exp (-t) := by
  have h := Real.mul_exp_neg_le_exp_neg_one (q/(2*t))
  have he : Real.exp (-1)≤1 := by simp
  have hy : (q/(2*t))*Real.exp (-(q/(2*t)))≤1 := h.trans he
  have hmul := mul_le_mul_of_nonneg_left hy (show 0≤2/q by positivity)
  have hid : (2/q)*(q/(2*t)*Real.exp (-(q/(2*t))))=
      t⁻¹*Real.exp (-(q/(2*t))) := by field_simp
  rw [hid,mul_one] at hmul
  rw [sub_eq_add_neg,Real.exp_add]
  calc
    t⁻¹*(Real.exp (-t)*Real.exp (-(q/(2*t))))=
      (t⁻¹*Real.exp (-(q/(2*t))))*Real.exp (-t) := by ring
    _≤(2/q)*Real.exp (-t) := mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le

theorem laplaceRadialDensity_ne_top {q : ℝ} (hq : 0<q) : laplaceRadialDensity q≠∞ := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0<t at ht
    positivity)).mpr
  apply ((integrableOn_exp_neg_Ioi 0).const_mul (2/q)).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0<t at ht
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact laplace_radial_integrand_bound hq ht

theorem laplaceRadialDensity_zero : laplaceRadialDensity 0=∞ := by
  by_contra hn
  have hi : IntegrableOn (fun t : ℝ => t⁻¹*Real.exp (-t)) (Ioi 0) := by
    apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0<t at ht
      positivity)).mp
    simpa only [laplaceRadialDensity,zero_div,sub_zero] using hn
  have hi' : IntegrableOn (fun t : ℝ => t⁻¹*Real.exp (-t)) (Ioo 0 1) :=
    hi.mono_set (fun _ h => h.1)
  have hinv : IntegrableOn (fun t : ℝ => t⁻¹) (Ioo 0 1) := by
    apply (hi'.const_mul (Real.exp 1)).mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    change 0<t ∧ t<1 at ht
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht.1)]
    have he : 1≤Real.exp (1-t) := by simpa using Real.exp_le_exp.mpr (show 0≤1-t by linarith [ht.2])
    have h := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr ht.1.le)
    rw [Real.exp_sub,div_eq_mul_inv,← Real.exp_neg] at h
    nlinarith
  have hp : IntegrableOn (fun t : ℝ => t^(-1:ℝ)) (Ioo 0 1) := by
    simpa only [Real.rpow_neg_one] using hinv
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0:ℝ)<1 by norm_num)).mp hp
  linarith

theorem laplaceRadialDensity_tendsto_zero :
    Filter.Tendsto laplaceRadialDensity (nhds (0:ℝ)) (nhds ∞) := by
  have hf := lintegral_liminf_le (μ := (volume : Measure ℝ).restrict (Ioi 0))
    (u := nhds (0:ℝ)) (f := fun q t : ℝ => ENNReal.ofReal (t⁻¹*Real.exp (-t-q/(2*t))))
    (fun _ => by fun_prop)
  have he : (∫⁻ t in Ioi (0:ℝ), Filter.liminf
      (fun q : ℝ => ENNReal.ofReal (t⁻¹*Real.exp (-t-q/(2*t)))) (nhds 0))=
      laplaceRadialDensity 0 := by
    apply lintegral_congr
    intro t
    exact (show Continuous (fun q : ℝ => ENNReal.ofReal
      (t⁻¹*Real.exp (-t-q/(2*t)))) from ENNReal.continuous_ofReal.comp (by fun_prop)).continuousAt.tendsto.liminf_eq
  rw [he,laplaceRadialDensity_zero] at hf
  exact tendsto_of_le_liminf_of_limsup_le hf le_top

theorem laplaceRadialDensity_continuousAt {q : ℝ} (hq : 0<q) :
    ContinuousAt laplaceRadialDensity q := by
  apply tendsto_lintegral_filter_of_dominated_convergence
    (fun t : ℝ => ENNReal.ofReal (t⁻¹*Real.exp (-t-(q/2)/(2*t))))
  · exact Filter.Eventually.of_forall fun _ => by fun_prop
  · filter_upwards [Ioi_mem_nhds (show q/2<q by linarith)] with v hv
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0<t at ht
    change q/2<v at hv
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_right hv.le (show 0≤2*t by positivity)
    linarith
  · exact laplaceRadialDensity_ne_top (show 0<q/2 by positivity)
  · exact Filter.Eventually.of_forall fun t =>
      (ENNReal.continuous_ofReal.comp (show Continuous (fun v : ℝ =>
        t⁻¹*Real.exp (-t-v/(2*t))) by fun_prop)).continuousAt

end Verification
