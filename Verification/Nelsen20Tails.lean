import Verification.Nelsen20
import Copula.TailDependence.Derivative
import Copula.TailDependence.Examples

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n20Diagonal (θ t : ℝ) : ℝ :=
  if t = 0 then 0 else Real.log (2*Real.exp (t^(-θ))-Real.exp 1)^(-θ⁻¹)

theorem n20Diagonal_eq {θ : ℝ} (hθ : 0 < θ) (t : I) :
    n20Diagonal θ t = (nelsen20 θ hθ.le).diagonal t := by
  rw [Copula.diagonal, nelsen20_cdf hθ]
  by_cases ht : t = 0
  · simp [ht, n20Diagonal]
  · simp [n20Diagonal, ht, unitInterval.coe_ne_zero.mpr ht, two_mul]

theorem n20Diagonal_deriv_one {θ : ℝ} (hθ : 0 < θ) : HasDerivAt (n20Diagonal θ) 2 1 := by
  have hp := (hasDerivAt_id (1:ℝ)).rpow_const (p := -θ) (Or.inl one_ne_zero)
  have hx := hp.exp.const_mul 2 |>.sub_const (Real.exp 1)
  have he : 2*Real.exp ((1:ℝ)^(-θ))-Real.exp 1 = Real.exp 1 := by simp; ring
  have hl := hx.log (by change 2*Real.exp ((1:ℝ)^(-θ))-Real.exp 1 ≠ 0; rw [he]; exact Real.exp_ne_zero 1)
  have hr := hl.rpow_const (p := -θ⁻¹) (Or.inl (by
    change Real.log (2*Real.exp ((1:ℝ)^(-θ))-Real.exp 1) ≠ 0
    rw [he, Real.log_exp]; norm_num))
  have hd : HasDerivAt (fun t : ℝ => Real.log (2*Real.exp (t^(-θ))-Real.exp 1)^(-θ⁻¹)) 2 1 := by
    convert hr using 1
    · rfl
    · dsimp only [id_eq]
      rw [he, Real.log_exp]
      simp
      field_simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (by norm_num : (1:ℝ) ≠ 0)] with t ht
  simp [n20Diagonal, ht]

theorem nelsen20_upperTail_pos {θ : ℝ} (hθ : 0 < θ) :
    (nelsen20 θ hθ.le).HasUpperTailDependence 0 := by
  simpa only [sub_self] using hasUpperTailDependence_of_hasDerivWithinAt
    (n20Diagonal_eq hθ) (n20Diagonal_deriv_one hθ).hasDerivWithinAt

theorem nelsen20_lowerTail_bound {θ : ℝ} (hθ : 0 < θ) (t : I) (ht : 0 < (t:ℝ)) :
    (1+(t:ℝ)^θ*Real.log 2)^(-θ⁻¹) ≤ (nelsen20 θ hθ.le).lowerTailRatio t := by
  have hp : 1 ≤ (t:ℝ)^(-θ) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht t.property.2 (neg_nonpos.mpr hθ.le)
  have he := Real.exp_le_exp.mpr hp
  have hsum : 0 < 2*Real.exp ((t:ℝ)^(-θ))-Real.exp 1 := by linarith [Real.exp_pos 1]
  have hl : 0 < Real.log (2*Real.exp ((t:ℝ)^(-θ))-Real.exp 1) := by
    apply Real.log_pos
    have h := Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)
    linarith
  have hlog : Real.log (2*Real.exp ((t:ℝ)^(-θ))-Real.exp 1) ≤ Real.log 2+(t:ℝ)^(-θ) := by
    have hh := Real.log_le_log hsum (show 2*Real.exp ((t:ℝ)^(-θ))-Real.exp 1 ≤ 2*Real.exp ((t:ℝ)^(-θ)) by linarith [Real.exp_pos 1])
    simpa only [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] using hh
  have hpow := Real.rpow_le_rpow_of_nonpos hl hlog (neg_nonpos.mpr (inv_pos.mpr hθ).le)
  have hprod : Real.log 2+(t:ℝ)^(-θ) = (t:ℝ)^(-θ)*(1+(t:ℝ)^θ*Real.log 2) := by
    rw [Real.rpow_neg ht.le]
    have hn := (Real.rpow_pos_of_pos ht θ).ne'
    field_simp
    ring
  rw [hprod, Real.mul_rpow (Real.rpow_nonneg ht.le _) (by positivity), ← Real.rpow_mul ht.le,
    show -θ * -θ⁻¹ = 1 by field_simp, Real.rpow_one] at hpow
  have ht0 : t ≠ 0 := unitInterval.coe_ne_zero.mp ht.ne'
  unfold lowerTailRatio Copula.diagonal
  rw [nelsen20_cdf hθ]
  simp only [ht0, or_self, ite_false, ← two_mul]
  apply (le_div_iff₀ ht).mpr
  nlinarith only [hpow]

theorem nelsen20_lowerTail_pos {θ : ℝ} (hθ : 0 < θ) :
    (nelsen20 θ hθ.le).HasLowerTailDependence 1 := by
  have ht : Tendsto (fun t : I => (t:ℝ)) (𝓝[>] (0:I)) (𝓝 (0:ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp := ht.rpow_const (p := θ) (Or.inr hθ.le)
  have hb : Tendsto (fun t : I => (1+(t:ℝ)^θ*Real.log 2)^(-θ⁻¹)) (𝓝[>] (0:I)) (𝓝 (1:ℝ)) := by
    have hh := (tendsto_const_nhds.add (hp.mul_const (Real.log 2))).rpow_const (p := -θ⁻¹)
      (Or.inl (by simp [Real.zero_rpow hθ.ne'] : (1:ℝ)+0^θ*Real.log 2 ≠ 0))
    simpa [Real.zero_rpow hθ.ne'] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hb tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact nelsen20_lowerTail_bound hθ t ht
  · exact Eventually.of_forall fun t => ((nelsen20 θ hθ.le).lowerTailRatio_mem_Icc t).2

theorem nelsen20_tails (θ : ℝ) (hθ : 0 ≤ θ) :
    (nelsen20 θ hθ).HasLowerTailDependence (if θ = 0 then 0 else 1) ∧
      (nelsen20 θ hθ).HasUpperTailDependence 0 := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen20_zero]
    simp only [ite_true]
    exact ⟨hasLowerTailDependence_independence, hasUpperTailDependence_independence⟩
  · have hp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
    simp only [hz, ite_false]
    exact ⟨nelsen20_lowerTail_pos hp, nelsen20_upperTail_pos hp⟩

end Verification
