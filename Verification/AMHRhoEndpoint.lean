import Verification.AMHRhoLog
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem amh_log_quotient_integrable_one :
    IntervalIntegrable (fun w : ℝ => Real.log (1-w)/w) volume 0 1 := by
  let f : ℝ → ℝ := fun w => Real.log (1-w)
  have hd : HasDerivAt f (-1) 0 := by
    convert ((hasDerivAt_const (0:ℝ) 1).sub (hasDerivAt_id 0)).log (by norm_num) using 1 <;>
      simp [f]
  have hc : ContinuousOn (dslope f 0) (Icc (0:ℝ) (1/2)) := by
    intro w hw
    by_cases hz : w=0
    · subst w
      exact (continuousAt_dslope_same.mpr hd.differentiableAt).continuousWithinAt
    · apply ContinuousAt.continuousWithinAt
      apply (continuousAt_dslope_of_ne hz).mpr
      apply ContinuousAt.log (by fun_prop)
      have hp : 0<1-w := by linarith [hw.2]
      exact hp.ne'
  have hi : IntervalIntegrable (dslope f 0) volume 0 (1/2) := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hi' : IntervalIntegrable (fun w : ℝ => Real.log (1-w)/w) volume 0 (1/2) := by
    apply hi.congr_ae
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with w hw
    simp [dslope_of_ne f hw,slope,f,smul_eq_mul,div_eq_mul_inv,mul_comm]
  have hj : IntervalIntegrable (fun w : ℝ => Real.log (1-w)) volume (1/2) 1 := by
    convert ((intervalIntegral.intervalIntegrable_log' (a:=0) (b:=1/2)).comp_sub_left 1).symm using 1 <;> norm_num
  have hk : ContinuousOn (fun w : ℝ => w⁻¹) (uIcc (1/2:ℝ) 1) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro w hw
    have hw' : w∈Icc (1/2:ℝ) 1 := by
      rw [uIcc_of_le (by norm_num)] at hw
      exact hw
    linarith [hw'.1]
  have hj' : IntervalIntegrable (fun w : ℝ => Real.log (1-w)/w) volume (1/2) 1 := by
    simpa [div_eq_mul_inv] using hj.mul_continuousOn hk
  exact hi'.trans hj'

theorem amhRhoBoundary_tendsto_one :
    Tendsto (amhRhoBoundary 1) (nhdsWithin 1 (Iio 1)) (nhds (-2)) := by
  have he : amhRhoBoundary 1 = fun w : ℝ =>
      ((1-w)*Real.log (1-w))*(-(1+w)/w)-2*w := by
    funext w
    by_cases hw : w=0
    · subst w; simp [amhRhoBoundary]
    · unfold amhRhoBoundary
      simp only [one_pow,one_mul,sub_self,zero_add,div_one]
      field_simp
      ring
  rw [he]
  have hc : ContinuousAt (fun w : ℝ => ((1-w)*Real.log (1-w))*(-(1+w)/w)-2*w) 1 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.mul
      · exact Real.continuous_mul_log.continuousAt.comp (by fun_prop)
      · fun_prop (disch := norm_num)
    · fun_prop
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

theorem amhRhoIntegrand_integral_one :
    (∫ w in (0:ℝ)..1, amhRhoIntegrand 1 w)=
      -2*(∫ w in (0:ℝ)..1, Real.log (1-w)/w)-3 := by
  have hi := amhRhoIntegrand_integrable_of_le_one (θ:=1) (by norm_num) le_rfl (by norm_num)
  have hj := amh_log_quotient_integrable_one
  have hderiv (w : ℝ) (hw : w∈Ioo (0:ℝ) 1) :
      HasDerivAt (amhRhoBoundary 1) (amhRhoIntegrand 1 w+2*(Real.log (1-w)/w)) w := by
    simpa [amhRhoIntegrand,show (1:ℝ)+1=2 by norm_num] using amhRhoBoundary_deriv 1 w (by norm_num) hw.1.ne'
      (by simpa using (sub_pos.mpr hw.2).ne')
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    hderiv (hi.add (hj.const_mul 2)) (amhRhoBoundary_tendsto_zero 1 (by norm_num)) amhRhoBoundary_tendsto_one
  rw [intervalIntegral.integral_add hi (hj.const_mul _),intervalIntegral.integral_const_mul] at hh
  norm_num at hh
  linarith

theorem amh_spearmanRho_one :
    (amh 1 (by norm_num) le_rfl).spearmanRho=
      24*(∫ t in (1:ℝ)..0, Real.log t/(1-t))-39 := by
  rw [amh_spearmanRho_integral_of_le_one (by norm_num) le_rfl (by norm_num)]
  have he : (fun v : I => (v:ℝ)/(1*(1-(v:ℝ)))+
      (v:ℝ)*(1-1*(1-(v:ℝ)))/(1*(1-(v:ℝ)))^2*Real.log (1-1*(1-(v:ℝ))))=
      fun v : I => amhRhoIntegrand 1 (1-(v:ℝ)) := by
    funext v
    simp only [amhRhoIntegrand,sub_sub_cancel]
  rw [he,Copula.integral_unitInterval (fun v => amhRhoIntegrand 1 (1-v)),
    intervalIntegral.integral_comp_sub_left]
  norm_num only [sub_self,sub_zero]
  rw [amhRhoIntegrand_integral_one]
  have hh := amh_log_integral_substitution 1 (by norm_num)
  simp only [one_mul,sub_self] at hh
  rw [hh]
  ring

theorem amh_spearmanRho_closed {θ : ℝ} (hmin : -1≤θ) (hmax : θ≤1) (h0 : θ≠0) :
    (amh θ hmin hmax).spearmanRho=
      12*(1+θ)*(∫ t in (1:ℝ)..(1-θ), Real.log t/(1-t))/θ^2-
        24*(1-θ)*Real.log (1-θ)/θ^2-3*(θ+12)/θ := by
  by_cases h1 : θ=1
  · subst θ
    rw [amh_spearmanRho_one]
    norm_num
  · exact amh_spearmanRho hmin (lt_of_le_of_ne hmax h1) h0

end Verification
