import Verification.Nelsen10Dependence
import Mathlib.Analysis.Calculus.DSlope

open ProbabilityTheory Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n10LogDen (u v t : ℝ) : ℝ :=
  Real.log (1+(1-Real.exp (t*Real.log u))*(1-Real.exp (t*Real.log v)))

theorem n10LogDen_deriv_zero (u v : ℝ) : HasDerivAt (n10LogDen u v) 0 0 := by
  have hu := (((hasDerivAt_id (0:ℝ)).mul_const (Real.log u)).exp).const_sub 1
  have hv := (((hasDerivAt_id (0:ℝ)).mul_const (Real.log v)).exp).const_sub 1
  have hh := ((hu.mul hv).const_add 1).log (by norm_num)
  convert hh using 1
  · rfl
  · norm_num

theorem nelsen10_continuousAt_zero (u v : I) :
    ContinuousAt (fun θ : I => (nelsen10 θ).cdf ![u,v]) 0 := by
  by_cases hu : u = 0
  · subst u
    simpa using (continuousAt_const : ContinuousAt (fun _ : I => (0:ℝ)) 0)
  by_cases hv : v = 0
  · subst v
    have he (θ : I) : (nelsen10 θ).cdf ![u,0] = 0 :=
      Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)
    simpa only [he] using (continuousAt_const : ContinuousAt (fun _ : I => (0:ℝ)) 0)
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  let f : ℝ → ℝ := fun t => (u:ℝ)*v*Real.exp (-dslope (n10LogDen u v) 0 t)
  have hc : ContinuousAt f 0 := by
    have hs : ContinuousAt (fun t => -dslope (n10LogDen u v) 0 t) 0 :=
      (continuousAt_dslope_same.mpr (n10LogDen_deriv_zero u v).differentiableAt).neg
    exact continuousAt_const.mul (Real.continuous_exp.continuousAt.comp hs)
  have he (θ : I) : (nelsen10 θ).cdf ![u,v] = f θ := by
    by_cases hz : (θ:ℝ) = 0
    · have hθ : θ = 0 := Subtype.ext hz
      subst θ
      simp [f, nelsen10_zero, dslope_same, (n10LogDen_deriv_zero u v).deriv,
        cdf_independence, Fin.prod_univ_two]
    have hp : 0 < (θ:ℝ) := lt_of_le_of_ne θ.property.1 (Ne.symm hz)
    rw [nelsen10_section θ u v hp]
    dsimp [f, n10Section]
    rw [dslope_of_ne _ hz, slope_def_field]
    have hden : 0 < n10Base θ v u := lt_of_lt_of_le zero_lt_one
      (n10Base_ge_one θ.property.1 v u.property)
    rw [Real.rpow_def_of_pos hden]
    have heq : n10LogDen u v θ = Real.log (n10Base θ v u) := by
      unfold n10LogDen n10Base
      rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos hv0]
      simp only [mul_comm (θ:ℝ)]
    rw [heq]
    simp only [n10LogDen, zero_mul, Real.exp_zero, sub_self, mul_zero, add_zero,
      Real.log_one, sub_zero]
    have ha : Real.log (n10Base θ v u)*(-(θ:ℝ)⁻¹) = - (Real.log (n10Base θ v u)/(θ:ℝ)) := by ring
    rw [ha]
    ring
  simp_rw [he]
  exact hc.comp (f := fun θ : I => (θ:ℝ)) (x := (0:I)) continuous_subtype_val.continuousAt

end Verification
