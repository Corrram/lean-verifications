import Verification.Nelsen13
import Mathlib.Analysis.Calculus.DSlope

open ProbabilityTheory Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n13LogBase (a b t : ℝ) : ℝ :=
  Real.log (Real.exp (t*Real.log a)+Real.exp (t*Real.log b)-1)

theorem n13LogBase_deriv_zero (a b : ℝ) :
    HasDerivAt (n13LogBase a b) (Real.log a+Real.log b) 0 := by
  have ha := ((hasDerivAt_id (0:ℝ)).mul_const (Real.log a)).exp
  have hb := ((hasDerivAt_id (0:ℝ)).mul_const (Real.log b)).exp
  have hh := ((ha.add hb).sub_const 1).log (by norm_num)
  convert hh using 1
  · rfl
  · norm_num

theorem nelsen13_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun z => (nelsen13 (θ z) (hθ z)).cdf ![u,v]) l
      (𝓝 ((gumbelBarnett 1).cdf ![u,v])) := by
  by_cases hu : u = 0
  · subst u
    simpa using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))
  by_cases hv : v = 0
  · subst v
    have he (C : Copula 2) : C.cdf ![u,0] = 0 :=
      Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)
    simpa [he] using (tendsto_const_nhds : Tendsto (fun _ : α => (0:ℝ)) l (𝓝 0))
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  let a : ℝ := 1-Real.log (u:ℝ)
  let b : ℝ := 1-Real.log (v:ℝ)
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (n13_inv_base u)
  have hb : 0 < b := lt_of_lt_of_le zero_lt_one (n13_inv_base v)
  let f : ℝ → ℝ := fun t => Real.exp (1-Real.exp (dslope (n13LogBase a b) 0 t))
  have hs := continuousAt_dslope_same.mpr (n13LogBase_deriv_zero a b).differentiableAt
  have hc : ContinuousAt f 0 := Real.continuous_exp.continuousAt.comp
    (continuousAt_const.sub (Real.continuous_exp.continuousAt.comp hs))
  have hf0 : f 0 = (gumbelBarnett 1).cdf ![u,v] := by
    dsimp [f]
    rw [dslope_same, (n13LogBase_deriv_zero a b).deriv, Real.exp_add,
      Real.exp_log ha, Real.exp_log hb, gumbelBarnett_cdf]
    have he : 1-a*b = Real.log (u:ℝ)+Real.log (v:ℝ)-Real.log (u:ℝ)*Real.log (v:ℝ) := by
      dsimp [a,b]; ring
    rw [he, Real.exp_sub, Real.exp_add, Real.exp_log hu0, Real.exp_log hv0]
    simp [Real.exp_neg, div_eq_mul_inv]
  have he (z : α) : (nelsen13 (θ z) (hθ z)).cdf ![u,v] = f (θ z) := by
    by_cases hz : θ z = 0
    · simp [nelsen13, hz, hf0]
    have hp : 0 < θ z := lt_of_le_of_ne (hθ z) (Ne.symm hz)
    rw [nelsen13_cdf (θ z) hp]
    simp only [hu, hv, or_self, ite_false]
    have hbase : 0 < a^(θ z)+b^(θ z)-1 := by
      linarith [Real.one_le_rpow (n13_inv_base u) hp.le,
        Real.one_le_rpow (n13_inv_base v) hp.le]
    change Real.exp (1-(a^(θ z)+b^(θ z)-1)^(θ z)⁻¹) = _
    rw [Real.rpow_def_of_pos hbase]
    dsimp [f]
    rw [dslope_of_ne _ hz, slope_def_field]
    simp only [n13LogBase, zero_mul, Real.exp_zero, add_sub_cancel_left,
      Real.log_one, sub_zero, div_eq_mul_inv]
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb]
    simp only [mul_comm (θ z)]
  simpa only [Function.comp_def, ← he, hf0] using hc.tendsto.comp hlim

end Verification
