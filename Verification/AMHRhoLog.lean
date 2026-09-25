import Verification.AMHRho
import Mathlib.Analysis.Calculus.DSlope

open ProbabilityTheory MeasureTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem amh_log_quotient_integrable {θ : ℝ} (hθ : θ<1) :
    IntervalIntegrable (fun w : ℝ => Real.log (1-θ*w)/w) volume 0 1 := by
  let f : ℝ → ℝ := fun w => Real.log (1-θ*w)
  have hd : HasDerivAt f (-θ) 0 := by
    convert ((hasDerivAt_const (0:ℝ) 1).sub ((hasDerivAt_id 0).const_mul θ)).log (by norm_num) using 1 <;>
      simp [f]
  have hc : ContinuousOn (dslope f 0) (Icc (0:ℝ) 1) := by
    intro w hw
    by_cases hz : w=0
    · subst w
      exact (continuousAt_dslope_same.mpr hd.differentiableAt).continuousWithinAt
    · apply ContinuousAt.continuousWithinAt
      apply (continuousAt_dslope_of_ne hz).mpr
      apply ContinuousAt.log (by fun_prop)
      have hp : 0<1-θ*w := by
        by_cases ht : 0≤θ
        · nlinarith [mul_le_mul_of_nonneg_left hw.2 ht]
        · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) hw.1]
      exact hp.ne'
  have hi : IntervalIntegrable (dslope f 0) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  apply hi.congr_ae
  filter_upwards [ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with w hw
  simp [dslope_of_ne f hw,slope,f,smul_eq_mul,div_eq_mul_inv,mul_comm]

noncomputable def amhRhoBoundary (θ w : ℝ) : ℝ :=
  -Real.log (1-θ*w)/(θ^2*w)+(θ-1+θ*w)*Real.log (1-θ*w)/θ^2-2*w/θ

theorem amhRhoBoundary_deriv (θ w : ℝ) (hθ : θ≠0) (hw : w≠0) (hd : 1-θ*w≠0) :
    HasDerivAt (amhRhoBoundary θ)
      ((1-w)/(θ*w)+(1-w)*(1-θ*w)/(θ*w)^2*Real.log (1-θ*w)+
        (1+θ)/θ^2*(Real.log (1-θ*w)/w)) w := by
  have hl := ((hasDerivAt_const w 1).sub ((hasDerivAt_id w).const_mul θ)).log hd
  have hh := (((hl.neg).div ((hasDerivAt_id w).const_mul (θ^2))
    (mul_ne_zero (pow_ne_zero 2 hθ) hw)).add
      (((((hasDerivAt_id w).const_mul θ).const_add (θ-1)).mul hl).div_const (θ^2))).sub
    (((hasDerivAt_id w).const_mul 2).div_const θ)
  convert hh using 1
  · funext x; rfl
  · dsimp only [Pi.mul_apply,Pi.add_apply,Pi.sub_apply,Pi.neg_apply,id_eq]
    field_simp [hθ,hw,hd]
    have hd' : 1-w*θ≠0 := by simpa [mul_comm] using hd
    field_simp [hd']
    ring

theorem amhRhoBoundary_tendsto_zero (θ : ℝ) (hθ : θ≠0) :
    Tendsto (amhRhoBoundary θ) (nhdsWithin 0 (Ioi 0)) (nhds (1/θ)) := by
  have hd : HasDerivAt (fun w : ℝ => Real.log (1-θ*w)) (-θ) 0 := by
    convert ((hasDerivAt_const (0:ℝ) 1).sub ((hasDerivAt_id 0).const_mul θ)).log (by norm_num) using 1 <;>
      simp
  have hq : Tendsto (fun w : ℝ => Real.log (1-θ*w)/w) (nhdsWithin 0 (Ioi 0)) (nhds (-θ)) := by
    have he : slope (fun w : ℝ => Real.log (1-θ*w)) 0 =
        fun w => Real.log (1-θ*w)/w := by
      funext w
      simp [slope,smul_eq_mul,div_eq_mul_inv,mul_comm]
    rw [← he]
    exact hd.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)
  have hl : Tendsto (fun w : ℝ => Real.log (1-θ*w)) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hw : Tendsto (fun w : ℝ => w) (nhdsWithin 0 (Ioi 0)) (nhds 0) := nhdsWithin_le_nhds
  have hh := ((hq.neg.div_const (θ^2)).add
    ((((tendsto_const_nhds (x:=θ-1)).add (hw.const_mul θ)).mul hl).div_const (θ^2))).sub
    ((hw.const_mul 2).div_const θ)
  convert hh using 1
  · funext w
    unfold amhRhoBoundary
    ring
  · congr 1
    field_simp
    ring

noncomputable def amhRhoIntegrand (θ w : ℝ) : ℝ :=
  (1-w)/(θ*w)+(1-w)*(1-θ*w)/(θ*w)^2*Real.log (1-θ*w)

theorem amhRhoIntegrand_integrable_of_le_one {θ : ℝ} (hmin : -1≤θ) (hmax : θ≤1) (h0 : θ≠0) :
    IntervalIntegrable (amhRhoIntegrand θ) volume 0 1 := by
  apply (intervalIntegrable_const (c:=(1:ℝ))).mono_fun' (by unfold amhRhoIntegrand; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 1)] with w hw hw1
  have hw' : w∈Ioc (0:ℝ) 1 := by simpa using hw
  let v : I := ⟨1-w,by constructor <;> linarith [hw'.1,hw'.2]⟩
  have hv : (v:ℝ)≠1 := by dsimp [v]; linarith [hw'.1]
  have hvp : 0<(v:ℝ) := by dsimp [v]; exact sub_pos.mpr (lt_of_le_of_ne hw'.2 hw1)
  have he := integral_amh_cdf_section_of_den_pos hmin hmax h0 v hv
    (fun _ hu => amhDen_pos_of_pos_right hmax hu v.property hvp)
  have he' : amhRhoIntegrand θ w=∫ u : I, (amh θ hmin hmax).cdf ![u,v] := by
    rw [he]
    simp only [v,sub_sub_cancel]
    rfl
  rw [he',Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun u => Copula.cdf_nonneg _ _))]
  calc
    _ ≤ ∫ _u : I, (1:ℝ) := integral_mono
      (Copula.integrable_continuous_unit volume ((amh θ hmin hmax).continuous_cdf.comp (by fun_prop)))
      (integrable_const 1) (fun u => Copula.cdf_le_one _ _)
    _ = 1 := by simp

theorem amhRhoIntegrand_integrable {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    IntervalIntegrable (amhRhoIntegrand θ) volume 0 1 :=
  amhRhoIntegrand_integrable_of_le_one hmin hmax.le h0

theorem amhRhoIntegrand_integral {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    (∫ w in (0:ℝ)..1, amhRhoIntegrand θ w)=
      -(1+θ)/θ^2*(∫ w in (0:ℝ)..1, Real.log (1-θ*w)/w)-
        2*(1-θ)*Real.log (1-θ)/θ^2-3/θ := by
  have hi := amhRhoIntegrand_integrable hmin hmax h0
  have hj := amh_log_quotient_integrable hmax
  have hderiv (w : ℝ) (hw : w∈Ioo (0:ℝ) 1) :=
    amhRhoBoundary_deriv θ w h0 hw.1.ne' (show 1-θ*w≠0 by
      have hh := amhDen_pos_lt_one hmax (show (0:ℝ)∈Icc 0 1 by norm_num)
        (show 1-w∈Icc (0:ℝ) 1 by constructor <;> linarith [hw.1,hw.2])
      simpa [amhDen] using hh.ne')
  have hb : Tendsto (amhRhoBoundary θ) (nhdsWithin 1 (Iio 1))
      (nhds (amhRhoBoundary θ 1)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    unfold amhRhoBoundary
    fun_prop (disch := simp [h0,ne_of_gt (sub_pos.mpr hmax)])
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one
    hderiv (hi.add (hj.const_mul ((1+θ)/θ^2))) (amhRhoBoundary_tendsto_zero θ h0) hb
  change (∫ w in (0:ℝ)..1, amhRhoIntegrand θ w+(1+θ)/θ^2*(Real.log (1-θ*w)/w))=
    amhRhoBoundary θ 1-1/θ at hh
  rw [intervalIntegral.integral_add hi (hj.const_mul _),intervalIntegral.integral_const_mul] at hh
  unfold amhRhoBoundary at hh
  simp only [mul_one] at hh
  linear_combination hh

theorem amh_spearmanRho_log_integral {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    (amh θ hmin hmax.le).spearmanRho=
      -12*(1+θ)/θ^2*(∫ w in (0:ℝ)..1, Real.log (1-θ*w)/w)-
        24*(1-θ)*Real.log (1-θ)/θ^2-3*(θ+12)/θ := by
  rw [amh_spearmanRho_integral hmin hmax h0]
  have he : (fun v : I => (v:ℝ)/(θ*(1-(v:ℝ)))+
      (v:ℝ)*(1-θ*(1-(v:ℝ)))/(θ*(1-(v:ℝ)))^2*Real.log (1-θ*(1-(v:ℝ))))=
      fun v : I => amhRhoIntegrand θ (1-(v:ℝ)) := by
    funext v
    simp only [amhRhoIntegrand,sub_sub_cancel]
  rw [he,Copula.integral_unitInterval (fun v => amhRhoIntegrand θ (1-v)),
    intervalIntegral.integral_comp_sub_left]
  norm_num only [sub_self,sub_zero]
  rw [amhRhoIntegrand_integral hmin hmax h0]
  field_simp
  ring

theorem amh_log_integral_substitution (θ : ℝ) (h0 : θ≠0) :
    (∫ w in (0:ℝ)..1, Real.log (1-θ*w)/w)=
      -(∫ t in (1:ℝ)..(1-θ), Real.log t/(1-t)) := by
  have he : (fun w : ℝ => Real.log (1-θ*w)/w)=
      fun w : ℝ => θ*(Real.log (1-θ*w)/(1-(1-θ*w))) := by
    funext w
    simp only [sub_sub_cancel]
    field_simp
  rw [he,intervalIntegral.integral_const_mul]
  have hh := intervalIntegral.integral_comp_sub_mul (fun t : ℝ => Real.log t/(1-t)) h0 1
    (a:=0) (b:=1)
  simp only [mul_zero,mul_one,sub_zero] at hh
  rw [hh]
  rw [smul_eq_mul]
  rw [← mul_assoc,mul_inv_cancel₀ h0,one_mul,intervalIntegral.integral_symm]

theorem amh_spearmanRho {θ : ℝ} (hmin : -1≤θ) (hmax : θ<1) (h0 : θ≠0) :
    (amh θ hmin hmax.le).spearmanRho=
      12*(1+θ)*(∫ t in (1:ℝ)..(1-θ), Real.log t/(1-t))/θ^2-
        24*(1-θ)*Real.log (1-θ)/θ^2-3*(θ+12)/θ := by
  rw [amh_spearmanRho_log_integral hmin hmax h0,amh_log_integral_substitution θ h0]
  ring

end Verification
