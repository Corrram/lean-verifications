import Verification.Nelsen11
import Mathlib.Analysis.Calculus.DSlope

open ProbabilityTheory Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n11Base (u v t : ℝ) : ℝ :=
  Real.exp (t*Real.log u)*Real.exp (t*Real.log v)-
    2*(1-Real.exp (t*Real.log u))*(1-Real.exp (t*Real.log v))

noncomputable def n11LogBase (u v t : ℝ) : ℝ := Real.log (n11Base u v t)

theorem n11Base_zero (u v : ℝ) : n11Base u v 0 = 1 := by simp [n11Base]

theorem n11LogBase_deriv_zero (u v : ℝ) :
    HasDerivAt (n11LogBase u v) (Real.log u+Real.log v) 0 := by
  have hu := ((hasDerivAt_id (0:ℝ)).mul_const (Real.log u)).exp
  have hv := ((hasDerivAt_id (0:ℝ)).mul_const (Real.log v)).exp
  have hh := (hu.mul hv).sub (((hu.const_sub 1).const_mul 2).mul (hv.const_sub 1))
  have hl := hh.log (by norm_num)
  convert hl using 1
  · rfl
  · norm_num

theorem nelsen11_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ0 : ∀ z, 0 ≤ θ z) (hθ1 : ∀ z, θ z ≤ 1/2)
    (hlim : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun z => (nelsen11 (θ z) (hθ0 z) (hθ1 z)).cdf ![u,v]) l (𝓝 ((u:ℝ)*v)) := by
  by_cases hu : u = 0
  · subst u
    simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))
  by_cases hv : v = 0
  · subst v
    have he (z : α) : (nelsen11 (θ z) (hθ0 z) (hθ1 z)).cdf ![u,0] = 0 :=
      Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)
    simpa [he] using
      (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  let f : ℝ → ℝ := fun t => Real.exp (dslope (n11LogBase u v) 0 t)
  have hc : ContinuousAt f 0 := Real.continuous_exp.continuousAt.comp
    (continuousAt_dslope_same.mpr (n11LogBase_deriv_zero u v).differentiableAt)
  have hf0 : f 0 = (u:ℝ)*v := by
    dsimp [f]
    rw [dslope_same, (n11LogBase_deriv_zero u v).deriv, Real.exp_add,
      Real.exp_log hu0, Real.exp_log hv0]
  have hf : Tendsto (fun z => f (θ z)) l (𝓝 ((u:ℝ)*v)) := by
    simpa only [Function.comp_def, hf0] using hc.tendsto.comp hlim
  have hbcont : Continuous (n11Base u v) := by unfold n11Base; fun_prop
  have hpos : ∀ᶠ z in l, 0 < n11Base u v (θ z) :=
    ((hbcont.tendsto 0).comp hlim).eventually
      (lt_mem_nhds (show 0 < n11Base u v 0 by rw [n11Base_zero]; norm_num))
  have he : (fun z => (nelsen11 (θ z) (hθ0 z) (hθ1 z)).cdf ![u,v]) =ᶠ[l]
      fun z => f (θ z) := by
    filter_upwards [hpos] with z hz
    by_cases ht : θ z = 0
    · simp [nelsen11, ht, hf0, cdf_independence, Fin.prod_univ_two]
    have hp : 0 < θ z := lt_of_le_of_ne (hθ0 z) (Ne.symm ht)
    rw [nelsen11_cdf (θ z) hp (hθ1 z)]
    have heq : (u:ℝ)^(θ z)*(v:ℝ)^(θ z)-2*(1-(u:ℝ)^(θ z))*(1-(v:ℝ)^(θ z)) =
        n11Base u v (θ z) := by
      unfold n11Base
      rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos hv0]
      simp only [mul_comm (θ z)]
    rw [heq, max_eq_right hz.le, Real.rpow_def_of_pos hz]
    dsimp [f]
    rw [dslope_of_ne _ ht, slope_def_field]
    simp only [n11LogBase, n11Base_zero, Real.log_one, sub_zero, div_eq_mul_inv]
  exact (tendsto_congr' he).mpr hf

end Verification
