import Verification.Nelsen18Dependence
import Copula.TailDependence.Quadrant

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen18_upperTail (θ : ℝ) (hθ : 2 ≤ θ) : (nelsen18 θ hθ).HasUpperTailDependence 1 := by
  have hp : 0 < θ := by linarith
  have ht : Tendsto (fun t : I => (t:ℝ)) (𝓝[>] (0:I)) (𝓝 0) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hd : Tendsto (fun t : I => θ-(t:ℝ)*Real.log 2) (𝓝[>] (0:I)) (𝓝 θ) := by
    simpa using (ht.mul_const (Real.log 2)).const_sub θ
  have hf : Tendsto (fun t : I => 1-θ*(t:ℝ)/(θ-(t:ℝ)*Real.log 2)) (𝓝[>] (0:I)) (𝓝 1) := by
    simpa using (((ht.const_mul θ).div hd hp.ne').const_sub 1)
  have hr : Tendsto (fun t : I => 2-θ/(θ-(t:ℝ)*Real.log 2)) (𝓝[>] (0:I)) (𝓝 1) := by
    have hh := (((tendsto_const_nhds (x := θ)).div hd hp.ne').const_sub 2)
    norm_num [hp.ne'] at hh
    exact hh
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin,hd.eventually (Ioi_mem_nhds hp),hf.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))]
    with t ht0 hd0 hf0
  have htpos : 0 < (t:ℝ) := ht0
  have hu : unitInterval.symm t < 1 := by
    change 1-(t:ℝ) < 1
    linarith
  have he := nelsen18_cdf_of_lt_one θ hθ (unitInterval.symm t) (unitInterval.symm t) hu hu
  simp only [unitInterval.coe_symm_eq,sub_sub_cancel_left] at he
  have hl : Real.log (Real.exp (θ/(-(t:ℝ)))+Real.exp (θ/(-(t:ℝ)))) = Real.log 2-θ/(t:ℝ) := by
    rw [← two_mul,Real.log_mul (by norm_num) (Real.exp_pos _).ne',Real.log_exp,div_neg]
    ring
  rw [hl] at he
  have hq : 1+θ/(Real.log 2-θ/(t:ℝ)) = 1-θ*(t:ℝ)/(θ-(t:ℝ)*Real.log 2) := by
    have hh : Real.log 2-θ/(t:ℝ) = -(θ-(t:ℝ)*Real.log 2)/(t:ℝ) := by
      field_simp
      ring
    rw [hh,div_div_eq_mul_div,div_neg]
    ring
  rw [hq,max_eq_right hf0.le] at he
  rw [upperTailRatio_eq,Copula.diagonal,he]
  field_simp
  ring

theorem nelsen18_not_nqd (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (nelsen18 θ hθ).IsNQD := by
  intro h
  have hz := isNQD_hasUpperTailDependence_zero h
  have hp := nelsen18_upperTail θ hθ
  let : NeBot (𝓝[>] (0:I)) := tailFilter_neBot
  have he := tendsto_nhds_unique hz hp
  norm_num at he

theorem nelsen18_not_cd (θ : ℝ) (hθ : 2 ≤ θ) : ¬ (nelsen18 θ hθ).IsCD :=
  fun h => nelsen18_not_nqd θ hθ h.isNQD

end Verification
