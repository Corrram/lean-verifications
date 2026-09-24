import Verification.Nelsen19
import Copula.TailDependence.Derivative
import Copula.TailDependence.Clayton

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen19_lowerTail_bound {θ : ℝ} (hθ : 0 < θ) (t : I) (ht : 0 < (t:ℝ)) :
    θ/(θ+(t:ℝ)*Real.log 2) ≤ (nelsen19 θ hθ.le).lowerTailRatio t := by
  have htn : t ≠ 0 := unitInterval.coe_ne_zero.mp ht.ne'
  have he : Real.exp θ ≤ Real.exp (θ/(t:ℝ)) := Real.exp_le_exp.mpr
    ((le_div_iff₀ ht).mpr (mul_le_of_le_one_right hθ.le t.property.2))
  have hex : 0 < 2*Real.exp (θ/(t:ℝ))-Real.exp θ := by linarith [Real.exp_pos (θ/(t:ℝ))]
  have hl : 0 < Real.log (2*Real.exp (θ/(t:ℝ))-Real.exp θ) := by
    apply Real.log_pos
    have hp := Real.one_lt_exp_iff.mpr hθ
    linarith
  have hlog : Real.log (2*Real.exp (θ/(t:ℝ))-Real.exp θ) ≤ Real.log 2+θ/(t:ℝ) := by
    have hh : Real.log (2*Real.exp (θ/(t:ℝ))) = Real.log 2+θ/(t:ℝ) := by
      rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
    rw [← hh]
    apply Real.log_le_log hex
    linarith [Real.exp_pos θ]
  have hden : 0 < θ+(t:ℝ)*Real.log 2 := by
    have hh : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    positivity
  have hb : (t:ℝ)*Real.log (2*Real.exp (θ/(t:ℝ))-Real.exp θ) ≤ θ+(t:ℝ)*Real.log 2 := by
    have hh := mul_le_mul_of_nonneg_left hlog ht.le
    field_simp at hh
    nlinarith
  unfold lowerTailRatio Copula.diagonal
  rw [nelsen19_cdf hθ]
  simp only [htn, or_self, ite_false, ← two_mul]
  rw [div_div, mul_comm (Real.log _)]
  exact div_le_div_of_nonneg_left hθ.le (mul_pos ht hl) hb

theorem nelsen19_lowerTail_pos {θ : ℝ} (hθ : 0 < θ) :
    (nelsen19 θ hθ.le).HasLowerTailDependence 1 := by
  have ht : Tendsto (fun t : I => (t:ℝ)) (𝓝[>] (0:I)) (𝓝 (0:ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun t : I => θ/(θ+(t:ℝ)*Real.log 2)) (𝓝[>] (0:I)) (𝓝 (1:ℝ)) := by
    have hh : Tendsto (fun t : I => θ/(θ+(t:ℝ)*Real.log 2))
        (𝓝[>] (0:I)) (𝓝 (θ/(θ+0*Real.log 2))) :=
      (tendsto_const_nhds (x := θ)).div
        (tendsto_const_nhds.add (ht.mul_const (Real.log 2))) (by simpa using hθ.ne')
    simpa only [zero_mul, add_zero, div_self hθ.ne'] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hb tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact nelsen19_lowerTail_bound hθ t ht
  · exact Eventually.of_forall fun t => ((nelsen19 θ hθ.le).lowerTailRatio_mem_Icc t).2

noncomputable def n19Diagonal (θ t : ℝ) : ℝ :=
  if t = 0 then 0 else θ/Real.log (2*Real.exp (θ/t)-Real.exp θ)

theorem n19Diagonal_eq {θ : ℝ} (hθ : 0 < θ) (t : I) :
    n19Diagonal θ t = (nelsen19 θ hθ.le).diagonal t := by
  rw [Copula.diagonal, nelsen19_cdf hθ]
  by_cases ht : t = 0
  · simp [ht, n19Diagonal]
  · simp [n19Diagonal, ht, unitInterval.coe_ne_zero.mpr ht, two_mul]

theorem n19Diagonal_deriv_one {θ : ℝ} (hθ : 0 < θ) : HasDerivAt (n19Diagonal θ) 2 1 := by
  have hx := (((hasDerivAt_const (1:ℝ) θ).div (hasDerivAt_id 1) one_ne_zero).exp).const_mul 2
  have he : 2*Real.exp (θ/1)-Real.exp θ = Real.exp θ := by simp; ring
  have hd := (hasDerivAt_const (1:ℝ) θ).div
    ((hx.sub_const (Real.exp θ)).log (by change 2*Real.exp (θ/1)-Real.exp θ ≠ 0; rw [he]; exact Real.exp_ne_zero θ))
    (by change Real.log (2*Real.exp (θ/1)-Real.exp θ) ≠ 0; rw [he, Real.log_exp]; exact hθ.ne')
  have hd' : HasDerivAt (fun t => θ/Real.log (2*Real.exp (θ/t)-Real.exp θ)) 2 1 := by
    convert hd using 1
    · rfl
    · dsimp only [Pi.div_apply, id_eq]
      rw [he, Real.log_exp]
      field_simp
      ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (by norm_num : (1:ℝ) ≠ 0)] with t ht
  simp [n19Diagonal, ht]

theorem nelsen19_upperTail_pos {θ : ℝ} (hθ : 0 < θ) :
    (nelsen19 θ hθ.le).HasUpperTailDependence 0 := by
  simpa only [sub_self] using hasUpperTailDependence_of_hasDerivWithinAt
    (n19Diagonal_eq hθ) (n19Diagonal_deriv_one hθ).hasDerivWithinAt

theorem nelsen19_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen19 θ hθ).HasLowerTailDependence (if θ = 0 then 1/2 else 1) ∧
      (nelsen19 θ hθ).HasUpperTailDependence 0 := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen19_zero]
    constructor
    · simpa [Real.rpow_neg_one] using hasLowerTailDependence_clayton_positive 1 (by norm_num)
    · exact hasUpperTailDependence_clayton_positive 1 (by norm_num)
  · have hp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
    simp only [hz, ite_false]
    exact ⟨nelsen19_lowerTail_pos hp, nelsen19_upperTail_pos hp⟩

end Verification
