import Verification.Nelsen19
import Copula.Dependence.Clayton
import Mathlib.Analysis.Calculus.Deriv.Slope

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen19_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (nelsen19 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((clayton 2 1 (by norm_num)).cdf ![u,v])) := by
  by_cases hu : u = 0
  · subst u; simp; exact tendsto_const_nhds
  by_cases hv : v = 0
  · subst v
    have hz (C : Copula 2) : C.cdf ![u,0] = 0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 (by simp)
    simp only [hz]; exact tendsto_const_nhds
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hv))
  let A : ℝ := 1/(u:ℝ)+1/(v:ℝ)-1
  have hA : 0 < A := by
    have h₁ : 1 ≤ 1/(u:ℝ) := (le_div_iff₀ hu0).mpr (by simpa using u.property.2)
    have h₂ : 1 ≤ 1/(v:ℝ) := (le_div_iff₀ hv0).mpr (by simpa using v.property.2)
    dsimp [A]; linarith
  let F : ℝ → ℝ := fun x => Real.log (Real.exp (x/(u:ℝ))+Real.exp (x/(v:ℝ))-Real.exp x)
  have hF0 : F 0 = 0 := by simp [F]
  have hd : HasDerivAt F A 0 := by
    have hh := ((((hasDerivAt_id (0:ℝ)).div_const (u:ℝ)).exp).add
      (((hasDerivAt_id (0:ℝ)).div_const (v:ℝ)).exp)).sub (Real.hasDerivAt_exp 0)
    convert hh.log (by norm_num : Real.exp (0/(u:ℝ))+Real.exp (0/(v:ℝ))-Real.exp 0 ≠ 0) using 1
    · rfl
    · simp [A]
  have hc : ContinuousAt (Function.update (fun x => F x/x) 0 A) 0 := by
    simpa only [hF0, sub_zero] using hd.continuousAt_div
  have hlim := (hc.inv₀ (by simpa using hA.ne')).tendsto.comp ht
  simp only [Pi.inv_apply, Function.update_self] at hlim
  have hClay : (clayton 2 1 (by norm_num)).cdf ![u,v] = A⁻¹ := by
    rw [cdf_clayton_two_pos 1 (by norm_num) u v hu0 hv0]
    simp [A, Real.rpow_neg_one]
  rw [hClay]
  apply hlim.congr'
  filter_upwards [] with a
  dsimp only [Function.comp_def, Pi.inv_apply]
  by_cases hz : θ a = 0
  · simp only [hz, Function.update_self, nelsen19, dite_true]
    exact hClay.symm
  · rw [Function.update_of_ne hz, nelsen19_cdf (lt_of_le_of_ne (hθ a) (Ne.symm hz))]
    simp only [hu, hv, or_self, ite_false, inv_div, F]

end Verification

