import Verification.Nelsen21Dependence
import Copula.TailDependence.Quadrant
import Mathlib.Analysis.Calculus.Deriv.Slope

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n21UpperCore (θ s : ℝ) : ℝ := 1-(2*(1-s)^θ⁻¹-1)^θ

theorem n21UpperCore_deriv_zero {θ : ℝ} (hθ : 0 < θ) : HasDerivAt (n21UpperCore θ) 2 0 := by
  have h₁ := (((hasDerivAt_id (0:ℝ)).const_sub 1).rpow_const (p := θ⁻¹) (Or.inl (by norm_num))).const_mul 2 |>.sub_const 1
  have hh := (h₁.rpow_const (p := θ) (Or.inl (by norm_num))).const_sub 1
  convert hh using 1
  · rfl
  · dsimp only [id_eq]
    norm_num
    field_simp

theorem nelsen21_upperTail (θ : ℝ) (hθ : 1 ≤ θ) :
    (nelsen21 θ hθ).HasUpperTailDependence (2-(2:ℝ)^θ⁻¹) := by
  have hp : 0 < θ := by linarith
  let Q : ℝ → ℝ := Function.update (fun s => n21UpperCore θ s/s) 0 2
  have hQ : ContinuousAt Q 0 := by
    have hd := n21UpperCore_deriv_zero hp
    have hz : n21UpperCore θ 0 = 0 := by norm_num [n21UpperCore]
    simpa only [hz,sub_zero] using hd.continuousAt_div
  have ht : Tendsto (fun t : I => (t:ℝ)) (𝓝[>] (0:I)) (𝓝 (0:ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun t : I => (t:ℝ)^θ) (𝓝[>] (0:I)) (𝓝 (0:ℝ)) := by
    simpa only [Real.zero_rpow hp.ne'] using ht.rpow_const (Or.inr hp.le)
  have hlim : Tendsto (fun t : I => 2-(Q ((t:ℝ)^θ))^θ⁻¹) (𝓝[>] (0:I)) (𝓝 (2-(2:ℝ)^θ⁻¹)) := by
    have hh := ((hQ.tendsto.comp hs).rpow_const (p := θ⁻¹) (Or.inr (inv_pos.mpr hp).le)).const_sub 2
    simpa only [Q,Function.update_self,Function.comp_def] using hh
  have hr : Tendsto (fun t : I => 2*(1-(t:ℝ)^θ)^θ⁻¹-1) (𝓝[>] (0:I)) (𝓝 (1:ℝ)) := by
    convert ((((tendsto_const_nhds (x := (1:ℝ))).sub hs).rpow_const (p := θ⁻¹) (Or.inr (inv_pos.mpr hp).le)).const_mul 2).sub_const 1 using 1
    norm_num
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,hr.eventually (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1))] with t ht0 hr0
  have htpos : 0 < (t:ℝ) := ht0
  have hspos : 0 < (t:ℝ)^θ := Real.rpow_pos_of_pos htpos _
  have hi := Real.rpow_le_one t.property.1 t.property.2 hp.le
  have hbase : 0 ≤ 1-(t:ℝ)^θ := by linarith
  have hroot : (1-(t:ℝ)^θ)^θ⁻¹ ≤ 1 := Real.rpow_le_one hbase
    (by linarith [hspos]) (inv_pos.mpr hp).le
  have hF : 0 ≤ n21UpperCore θ ((t:ℝ)^θ) := sub_nonneg.mpr
    (Real.rpow_le_one hr0.le (by linarith) hp.le)
  have he : (n21UpperCore θ ((t:ℝ)^θ)/(t:ℝ)^θ)^θ⁻¹ =
      (n21UpperCore θ ((t:ℝ)^θ))^θ⁻¹/(t:ℝ) := by
    rw [Real.div_rpow hF hspos.le,Real.rpow_rpow_inv t.property.1 hp.ne']
  rw [show Q ((t:ℝ)^θ) = n21UpperCore θ ((t:ℝ)^θ)/(t:ℝ)^θ by
    exact Function.update_of_ne hspos.ne' 2 _,he]
  rw [upperTailRatio_eq,Copula.diagonal,nelsen21_cdf_full]
  simp only [unitInterval.coe_symm_eq,sub_sub_cancel]
  rw [show (1-(t:ℝ)^θ)^θ⁻¹+(1-(t:ℝ)^θ)^θ⁻¹-1 = 2*(1-(t:ℝ)^θ)^θ⁻¹-1 by ring,
    max_eq_right hr0.le]
  dsimp [n21UpperCore]
  field_simp
  ring

theorem nelsen21_not_nqd_above_one (θ : ℝ) (hθ : 1 < θ) : ¬ (nelsen21 θ hθ.le).IsNQD := by
  intro h
  have hz := isNQD_hasUpperTailDependence_zero h
  have hp := nelsen21_upperTail θ hθ.le
  let : NeBot (𝓝[>] (0:I)) := tailFilter_neBot
  have he := tendsto_nhds_unique hz hp
  have hpow : (2:ℝ)^θ⁻¹ < 2 := by
    have hi : θ⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < θ)).mpr hθ
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hi
    simpa only [Real.rpow_one] using hh
  linarith

theorem nelsen21_isCD_iff (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen21 θ hθ).IsCD ↔ θ = 1 := by
  constructor
  · intro h
    by_contra hn
    exact nelsen21_not_nqd_above_one θ (lt_of_le_of_ne hθ (Ne.symm hn)) h.isNQD
  · intro h; subst θ
    rw [nelsen21_one]
    exact isCD_countermonotonic

theorem nelsen21_isNQD_iff (θ : ℝ) (hθ : 1 ≤ θ) : (nelsen21 θ hθ).IsNQD ↔ θ = 1 := by
  constructor
  · intro h
    by_contra hn
    exact nelsen21_not_nqd_above_one θ (lt_of_le_of_ne hθ (Ne.symm hn)) h
  · intro h; subst θ
    exact ((nelsen21_isCD_iff 1 (by norm_num)).mpr rfl).isNQD

end Verification
