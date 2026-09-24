import Verification.Nelsen17
import Mathlib.Analysis.Calculus.Deriv.Slope

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n17PowerSlope (x a : ℝ) : ℝ :=
  Function.update (fun a => (x^a-1)/a) 0 (Real.log x) a

theorem n17PowerSlope_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt (n17PowerSlope x) 0 := by
  have hd : HasDerivAt (fun a : ℝ => x^a-1) (Real.log x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_rpow hx).sub_const 1
  change ContinuousAt (Function.update (fun a => (x^a-1)/a) 0 (Real.log x)) 0
  simpa only [Real.rpow_zero, sub_self, sub_zero] using hd.continuousAt_div

theorem nelsen17_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, θ a ≠ 0) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (nelsen17 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 (Real.exp (Real.log (1+(u:ℝ))*Real.log (1+(v:ℝ))/Real.log 2)-1)) := by
  have hu : 0 < 1+(u:ℝ) := by linarith [u.property.1]
  have hv : 0 < 1+(v:ℝ) := by linarith [v.property.1]
  have h2 : Real.log (2:ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  let K : ℝ → ℝ := fun a => n17PowerSlope (1+(u:ℝ)) a*n17PowerSlope (1+(v:ℝ)) a/n17PowerSlope 2 a
  have hK : ContinuousAt K 0 :=
    ((n17PowerSlope_continuousAt hu).mul (n17PowerSlope_continuousAt hv)).div
      (n17PowerSlope_continuousAt (by norm_num : (0:ℝ) < 2)) (by simpa [n17PowerSlope] using h2)
  have hd : HasDerivAt (fun a => a*K a) (K 0) 0 := by
    apply hasDerivAt_iff_tendsto_slope_zero.mpr
    apply (hK.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with a ha
    have hn : a ≠ 0 := ha
    simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
    field_simp
  let F : ℝ → ℝ := fun a => Real.log (1+a*K a)
  have hF : HasDerivAt F (K 0) 0 := by
    simpa using (hd.const_add 1).log (by simp)
  have hF0 : F 0 = 0 := by simp [F]
  have hc : ContinuousAt (Function.update (fun a => F a/a) 0 (K 0)) 0 := by
    simpa only [hF0, sub_zero] using hF.continuousAt_div
  have ht' : Tendsto (fun a => -θ a) l (𝓝 (0:ℝ)) := by simpa using ht.neg
  have hlim := ((Real.continuous_exp.continuousAt.comp hc).tendsto.comp ht').sub_const 1
  have heq : K 0 = Real.log (1+(u:ℝ))*Real.log (1+(v:ℝ))/Real.log 2 := by simp [K,n17PowerSlope]
  simp only [Function.comp_def, Function.update_self] at hlim
  rw [← heq]
  apply hlim.congr'
  have hbase : ∀ᶠ a in l, 0 < 1+(-θ a)*K (-θ a) := by
    have hh := (((continuousAt_id.mul hK).const_add 1).tendsto.comp ht').eventually
      (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1+(0:ℝ)*K 0))
    exact hh
  filter_upwards [hbase] with a ha
  have hn := neg_ne_zero.mpr (hθ a)
  have hA := n17A_ne hn
  have hprod : (-θ a)*K (-θ a) =
      (((1+(u:ℝ))^(-θ a)-1)*((1+(v:ℝ))^(-θ a)-1))/((2:ℝ)^(-θ a)-1) := by
    dsimp [K,n17PowerSlope]
    rw [Function.update_of_ne hn,Function.update_of_ne hn,Function.update_of_ne hn]
    dsimp [n17A] at hA
    field_simp [hθ a]
  rw [Function.update_of_ne hn, nelsen17_cdf_full]
  rw [hprod] at ha
  rw [Real.rpow_def_of_pos ha]
  dsimp [F]
  rw [hprod]
  congr 2
  simp only [div_eq_mul_inv,inv_neg]

end Verification
