import Verification.Nelsen20Tails
import Mathlib.Analysis.Calculus.Deriv.Slope

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem nelsen20_tendsto_zero {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Tendsto θ l (𝓝 0)) (u v : I) :
    Tendsto (fun a => (nelsen20 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((independence 2).cdf ![u,v])) := by
  by_cases hu : u = 0
  · subst u; simp; exact tendsto_const_nhds
  by_cases hv : v = 0
  · subst v
    have hz (C : Copula 2) : C.cdf ![u,0] = 0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 (by simp)
    simp only [hz]; exact tendsto_const_nhds
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hv))
  let A : ℝ := -(Real.log (u:ℝ)+Real.log (v:ℝ))
  let F : ℝ → ℝ := fun x => Real.log (Real.log
    (Real.exp ((u:ℝ)^(-x))+Real.exp ((v:ℝ)^(-x))-Real.exp 1))
  have hF0 : F 0 = 0 := by simp [F]
  have hd : HasDerivAt F A 0 := by
    have hd₁ := (HasDerivAt.const_rpow hu0 (hasDerivAt_id (0:ℝ)).neg).exp
    have hd₂ := (HasDerivAt.const_rpow hv0 (hasDerivAt_id (0:ℝ)).neg).exp
    have hsum := (hd₁.add hd₂).sub_const (Real.exp 1)
    have hx : Real.exp ((u:ℝ)^(-(0:ℝ)))+Real.exp ((v:ℝ)^(-(0:ℝ)))-Real.exp 1 = Real.exp 1 := by simp
    have hlog := hsum.log (by simp)
    have hh := hlog.log (by simp)
    convert hh using 1
    · rfl
    · dsimp only [Pi.add_apply, Pi.neg_apply, id_eq]
      rw [hx, Real.log_exp]
      simp [A]
      field_simp
      ring
  have hc : ContinuousAt (Function.update (fun x => F x/x) 0 A) 0 := by
    simpa only [hF0, sub_zero] using hd.continuousAt_div
  have hlim := (Real.continuous_exp.continuousAt.comp hc.neg).tendsto.comp ht
  simp only [Function.comp_def, Pi.neg_apply, Function.update_self] at hlim
  have hInd : Real.exp (-A) = (independence 2).cdf ![u,v] := by
    simp [A, Real.exp_add, Real.exp_log hu0, Real.exp_log hv0, cdf_independence]
  rw [← hInd]
  apply hlim.congr'
  filter_upwards [] with a
  by_cases hz : θ a = 0
  · simp only [hz, Function.update_self, nelsen20, dite_true]
    exact hInd
  · rw [Function.update_of_ne hz, nelsen20_cdf (lt_of_le_of_ne (hθ a) (Ne.symm hz))]
    simp only [hu, hv, or_self, ite_false]
    have h₁ : Real.exp 1 ≤ Real.exp ((u:ℝ)^(-θ a)) := Real.exp_le_exp.mpr
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 u.property.2 (neg_nonpos.mpr (hθ a)))
    have h₂ : Real.exp 1 ≤ Real.exp ((v:ℝ)^(-θ a)) := Real.exp_le_exp.mpr
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv0 v.property.2 (neg_nonpos.mpr (hθ a)))
    have hl : 0 < Real.log (Real.exp ((u:ℝ)^(-θ a))+Real.exp ((v:ℝ)^(-θ a))-Real.exp 1) := by
      apply Real.log_pos
      have he := Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 1)
      linarith
    rw [Real.rpow_def_of_pos hl]
    congr 1
    dsimp [F]
    ring

theorem nelsen20_cdf_lower_bound {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (min u v:ℝ)*(1+Real.log 2)^(-θ⁻¹) ≤ (nelsen20 θ hθ.le).cdf ![u,v] := by
  let w : I := min u v
  change (w:ℝ)*(1+Real.log 2)^(-θ⁻¹) ≤ _
  by_cases hw : w = 0
  · simp only [hw, show ((0:I):ℝ) = 0 from rfl, zero_mul]
    exact (nelsen20 θ hθ.le).cdf_nonneg _
  have hp : 0 < (w:ℝ) := lt_of_le_of_ne w.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hw))
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hbase : 0 < 1+(w:ℝ)^θ*Real.log 2 := by positivity
  have hr := Real.rpow_le_rpow_of_nonpos hbase
    (show 1+(w:ℝ)^θ*Real.log 2 ≤ 1+Real.log 2 by
      have hh := mul_le_mul_of_nonneg_right (Real.rpow_le_one w.property.1 w.property.2 hθ.le) hlog.le
      linarith) (neg_nonpos.mpr (inv_pos.mpr hθ).le)
  have hh := mul_le_mul_of_nonneg_left (hr.trans (nelsen20_lowerTail_bound hθ w hp)) hp.le
  have he : (w:ℝ)*(nelsen20 θ hθ.le).lowerTailRatio w = (nelsen20 θ hθ.le).diagonal w := by
    unfold lowerTailRatio
    field_simp
  rw [he] at hh
  apply hh.trans
  apply (nelsen20 θ hθ.le).monotone_cdf
  intro i
  fin_cases i
  · exact min_le_left u v
  · exact min_le_right u v

theorem nelsen20_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 0 ≤ θ a) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (nelsen20 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((comonotonic 2).cdf ![u,v])) := by
  have hi : Tendsto (fun a => -(θ a)⁻¹) l (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def, neg_zero] using (tendsto_inv_atTop_zero.comp ht).neg
  have hp : Tendsto (fun a => (1+Real.log 2)^(-(θ a)⁻¹)) l (𝓝 (1:ℝ)) := by
    have hh := tendsto_const_nhds.rpow hi (Or.inl (show (1:ℝ)+Real.log 2 ≠ 0 by
      have hh := Real.log_pos (by norm_num : (1:ℝ) < 2)
      linarith))
    simpa only [Real.rpow_zero] using hh
  have hlo : Tendsto (fun a => (min u v:ℝ)*(1+Real.log 2)^(-(θ a)⁻¹)) l
      (𝓝 (min u v:ℝ)) := by simpa using hp.const_mul (min u v:ℝ)
  have he : (comonotonic 2).cdf ![u,v] = (min u v:ℝ) := by rw [cdf_comonotonic_two]; rfl
  rw [he]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [ht.eventually (eventually_gt_atTop (0:ℝ))] with a ha
    exact nelsen20_cdf_lower_bound ha u v
  · exact Eventually.of_forall fun a => le_min ((nelsen20 (θ a) (hθ a)).cdf_le_coord ![u,v] 0)
      ((nelsen20 (θ a) (hθ a)).cdf_le_coord ![u,v] 1)

end Verification
