import Verification.GammaPowerLaplace

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem gamma_integral_rpow {a b k : ℝ} (ha : 0<a) (hb : 0<b) (hak : 0<a+k) :
    Integrable (fun t : ℝ => t^k) (gammaMeasure a b) ∧
      (∫ t : ℝ, t^k ∂gammaMeasure a b)=b^a/Real.Gamma a*Real.Gamma (a+k)/b^(a+k) := by
  have he := lintegral_power_exp_gammaMeasure (d := 0) ha hb hak (by simpa using hb)
  simp only [zero_mul,neg_zero,Real.exp_zero,mul_one,add_zero] at he
  have hn : 0≤ᵐ[gammaMeasure a b] (fun t : ℝ => t^k) := by
    filter_upwards [ae_pos_gammaMeasure a b] with t ht
    exact (Real.rpow_pos_of_pos ht k).le
  have hi : Integrable (fun t : ℝ => t^k) (gammaMeasure a b) :=
    (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hn).mp (he.trans_ne ENNReal.ofReal_ne_top)
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at he
  have hh := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn),
    ENNReal.toReal_ofReal (show 0≤b^a/Real.Gamma a*Real.Gamma (a+k)/b^(a+k) by
      have := Real.Gamma_pos_of_pos ha
      have := Real.Gamma_pos_of_pos hak
      positivity)] using hh

theorem gammaPrecision_first_moment {a : ℝ} (ha : 0<a) :
    Integrable (fun t : ℝ => t) (gammaMeasure a a) ∧
      (∫ t : ℝ, t ∂gammaMeasure a a)=1 := by
  obtain ⟨hi,he⟩ := gamma_integral_rpow (k := 1) ha ha (by linarith)
  simp only [Real.rpow_one] at hi he
  refine ⟨hi,he.trans ?_⟩
  rw [Real.Gamma_add_one ha.ne',Real.rpow_add ha,Real.rpow_one]
  have hG := (Real.Gamma_pos_of_pos ha).ne'
  have hp := (Real.rpow_pos_of_pos ha a).ne'
  field_simp

theorem gammaPrecision_second_moment {a : ℝ} (ha : 0<a) :
    Integrable (fun t : ℝ => t^2) (gammaMeasure a a) ∧
      (∫ t : ℝ, t^2 ∂gammaMeasure a a)=1+a⁻¹ := by
  obtain ⟨hi,he⟩ := gamma_integral_rpow (k := 2) ha ha (by linarith)
  simp only [Real.rpow_two] at hi he
  refine ⟨hi,he.trans ?_⟩
  rw [show a+2=(a+1)+1 by ring,Real.Gamma_add_one (by linarith : a+1≠0),
    Real.Gamma_add_one ha.ne',Real.rpow_add ha,Real.rpow_add ha,Real.rpow_one]
  have hG := (Real.Gamma_pos_of_pos ha).ne'
  have hp := (Real.rpow_pos_of_pos ha a).ne'
  field_simp

theorem gammaPrecision_centered_second_moment {a : ℝ} (ha : 0<a) :
    Integrable (fun t : ℝ => (t-1)^2) (gammaMeasure a a) ∧
      (∫ t : ℝ, (t-1)^2 ∂gammaMeasure a a)=a⁻¹ := by
  let : IsProbabilityMeasure (gammaMeasure a a) := isProbabilityMeasure_gammaMeasure ha ha
  obtain ⟨h1,e1⟩ := gammaPrecision_first_moment ha
  obtain ⟨h2,e2⟩ := gammaPrecision_second_moment ha
  have he : (fun t : ℝ => (t-1)^2)=(fun t => t^2-2*t+1) := by funext t; ring
  rw [he]
  refine ⟨(h2.sub (h1.const_mul 2)).add (integrable_const 1),?_⟩
  have hs : Integrable (fun t : ℝ => t^2-2*t) (gammaMeasure a a) := h2.sub (h1.const_mul 2)
  have hm : Integrable (fun t : ℝ => 2*t) (gammaMeasure a a) := h1.const_mul 2
  rw [integral_add hs (integrable_const 1),integral_sub h2 hm,integral_const_mul,e1,e2]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  ring

end Verification
