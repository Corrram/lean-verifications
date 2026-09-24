import Verification.Nelsen13
import Verification.GumbelBarnettDependence
import Copula.TailDependence.Derivative
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open ProbabilityTheory Set Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n13Diagonal (θ t : ℝ) : ℝ :=
  if t = 0 then 0 else Real.exp (1-(2*(1-Real.log t)^θ-1)^θ⁻¹)

theorem n13Diagonal_eq (θ : ℝ) (hθ : 0 < θ) (t : I) :
    n13Diagonal θ t = (nelsen13 θ hθ.le).diagonal t := by
  rw [Copula.diagonal, nelsen13_cdf θ hθ]
  by_cases ht : t = 0
  · simp [ht, n13Diagonal]
  · have ht' : (t:ℝ) ≠ 0 := fun h => ht (Subtype.ext h)
    simp only [n13Diagonal, ht', ht, or_self, ite_false]
    congr 3
    ring

theorem n13Diagonal_deriv_one (θ : ℝ) (hθ : 0 < θ) :
    HasDerivAt (n13Diagonal θ) 2 1 := by
  have hl := (Real.hasDerivAt_log (by norm_num : (1:ℝ) ≠ 0)).const_sub 1
  have hp := hl.rpow_const (p := θ) (Or.inl (by norm_num))
  have hb := (hp.const_mul 2).sub_const 1
  have hr := hb.rpow_const (p := θ⁻¹) (Or.inl (by norm_num))
  have he := (hr.const_sub 1).exp
  have he' : HasDerivAt (fun t : ℝ => Real.exp (1-(2*(1-Real.log t)^θ-1)^θ⁻¹)) 2 1 := by
    convert he using 1
    norm_num [hθ.ne']
  apply he'.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (by norm_num : (1:ℝ) ≠ 0)] with t ht
  simp [n13Diagonal, ht]

theorem nelsen13_upperTail (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen13 θ hθ).HasUpperTailDependence 0 := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen13_zero]
    exact (gumbelBarnett_tails 1).2
  · have hp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
    simpa using Copula.hasUpperTailDependence_of_hasDerivWithinAt
      (n13Diagonal_eq θ hp) (n13Diagonal_deriv_one θ hp).hasDerivWithinAt

theorem nelsen13_lowerTail_pos (θ : ℝ) (hθ : 0 < θ) :
    (nelsen13 θ hθ.le).HasLowerTailDependence 0 := by
  let X : I → ℝ := fun t => 1-Real.log (t:ℝ)
  let c : ℝ := (3/2:ℝ)^θ⁻¹
  have hc : 1 < c := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hθ)
  have htlim : Tendsto (fun t : I => (t:ℝ)) (𝓝[>] (0:I)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have hlog := Real.tendsto_log_nhdsGT_zero.comp htlim
  have hX : Tendsto X (𝓝[>] (0:I)) atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hlog.eventually (eventually_le_atBot (1-b))] with t ht
    dsimp only [Function.comp_def] at ht
    dsimp [X]
    linarith
  have hpow := (tendsto_rpow_atTop hθ).comp hX
  have hbound : Tendsto (fun t => Real.exp ((1-c)*X t)) (𝓝[>] (0:I)) (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hX.const_mul_atTop_of_neg (by linarith))
  change Tendsto (fun t : I => (nelsen13 θ hθ.le).diagonal t / (t:ℝ)) _ _
  apply squeeze_zero' (Eventually.of_forall fun t => div_nonneg (by
    exact (nelsen13 θ hθ.le).cdf_nonneg _) t.property.1) ?_ hbound
  filter_upwards [self_mem_nhdsWithin, hpow.eventually (eventually_ge_atTop 2)] with t ht hp
  dsimp only [Function.comp_def] at hp
  have ht0 : 0 < (t:ℝ) := ht
  have hX0 : 0 ≤ X t := le_trans zero_le_one (n13_inv_base t)
  have hroot : c*X t ≤ (2*(X t)^θ-1)^θ⁻¹ := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (3/2:ℝ)*(X t)^θ)
      (show (3/2:ℝ)*(X t)^θ ≤ 2*(X t)^θ-1 by linarith) (inv_nonneg.mpr hθ.le)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hX0 _),
      Real.rpow_rpow_inv hX0 hθ.ne'] at hh
    exact hh
  rw [← n13Diagonal_eq θ hθ, n13Diagonal, ite_eq_right (by exact ht0.ne')]
  conv_lhs => rhs; rw [← Real.exp_log ht0]
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  change 1-(2*(X t)^θ-1)^θ⁻¹-Real.log (t:ℝ) ≤ (1-c)*X t
  dsimp [X] at hroot ⊢
  nlinarith

theorem nelsen13_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen13 θ hθ).HasLowerTailDependence 0 ∧
      (nelsen13 θ hθ).HasUpperTailDependence 0 := by
  refine ⟨?_, nelsen13_upperTail θ hθ⟩
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen13_zero]
    exact (gumbelBarnett_tails 1).1
  · exact nelsen13_lowerTail_pos θ (lt_of_le_of_ne hθ (Ne.symm hz))

end Verification
