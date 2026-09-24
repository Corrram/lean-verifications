import Verification.Nelsen21
import Copula.Diagonal
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem n21Core_upper_bound {θ t : ℝ} (hθ : 1 ≤ θ) (ht : t ∈ Icc 0 1) :
    n21Core θ t ≤ (1-t)^θ := by
  have hp : 0 < θ := by linarith
  have hi := n21_inner_mem hp ht
  have hh := Real.self_le_rpow_of_le_one hi.1 hi.2 ((inv_le_one₀ hp).mpr hθ)
  dsimp [n21Core]
  linarith

theorem n21Psi_lower_bound {θ s : ℝ} (hθ : 1 ≤ θ) (hs : 0 ≤ s) :
    1-(θ*s)^θ⁻¹ ≤ n21Psi θ s := by
  have hp : 0 < θ := by linarith
  have hm : min s (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_min hs zero_le_one,min_le_right _ _⟩
  have hh := one_add_mul_self_le_rpow_one_add (show -1 ≤ -min s (1:ℝ) by linarith [hm.2]) hθ
  have hB : 1-(1-min s 1)^θ ≤ θ*s := by
    have hm' := mul_le_mul_of_nonneg_left (min_le_left s (1:ℝ)) hp.le
    simp only [mul_neg,← sub_eq_add_neg] at hh
    linarith
  have hr := Real.rpow_le_rpow (n21_inner_mem hp hm).1 hB (inv_pos.mpr hp).le
  exact sub_le_sub_left hr 1

theorem n21_diagonal_formula (θ : ℝ) (hθ : 1 ≤ θ) (t : I) :
    (nelsen21 θ hθ).diagonal t = n21Psi θ (2*n21Core θ t) := by
  have hp : 0 < θ := by linarith
  by_cases ht : t = 0
  · subst t
    simp only [Copula.diagonal,cdf_two_zero_left]
    norm_num [n21Psi,n21Core,Real.zero_rpow (inv_ne_zero hp.ne'),Real.zero_rpow hp.ne']
  · rw [Copula.diagonal,nelsen21,BivariateGenerator.cdf_copula,BivariateGenerator.cdf]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,ht,or_self,ite_false]
    change n21Psi θ (n21Core θ t+n21Core θ t) = _
    rw [← two_mul]

theorem n21_diagonal_lower_bound (θ : ℝ) (hθ : 1 ≤ θ) (t : I) :
    1-(2*θ)^θ⁻¹*(1-(t:ℝ)) ≤ (nelsen21 θ hθ).diagonal t := by
  have hp : 0 < θ := by linarith
  have ht : 0 ≤ 1-(t:ℝ) := by linarith [t.property.2]
  have hpow := Real.rpow_nonneg ht θ
  have hh := n21Core_upper_bound hθ t.property
  have hm := (n21Generator θ hθ).antitone
    (show 0 ≤ 2*n21Core θ t by linarith [(n21Core_mem hp t.property).1])
    (show 0 ≤ 2*(1-(t:ℝ))^θ by positivity) (show 2*n21Core θ t ≤ 2*(1-(t:ℝ))^θ by linarith)
  have hb := (n21Psi_lower_bound hθ (show 0 ≤ 2*(1-(t:ℝ))^θ by positivity)).trans hm
  rw [n21_diagonal_formula θ hθ t]
  have he : (θ*(2*(1-(t:ℝ))^θ))^θ⁻¹ = (2*θ)^θ⁻¹*(1-(t:ℝ)) := by
    rw [show θ*(2*(1-(t:ℝ))^θ) = (2*θ)*(1-(t:ℝ))^θ by ring,
      Real.mul_rpow (by positivity) hpow,Real.rpow_rpow_inv ht hp.ne']
  rwa [he] at hb

theorem nelsen21_cdf_lower_bound (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) :
    1-(2*θ)^θ⁻¹*(1-(min u v:ℝ)) ≤ (nelsen21 θ hθ).cdf ![u,v] := by
  apply (n21_diagonal_lower_bound θ hθ (min u v)).trans
  apply (nelsen21 θ hθ).monotone_cdf
  intro i
  fin_cases i
  · exact min_le_left u v
  · exact min_le_right u v

theorem nelsen21_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (ht : Tendsto θ l atTop) (u v : I) :
    Tendsto (fun a => (nelsen21 (θ a) (hθ a)).cdf ![u,v]) l
      (𝓝 ((comonotonic 2).cdf ![u,v])) := by
  have hi : Tendsto (fun a => (θ a)⁻¹) l (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero.comp ht
  have h2 : Tendsto (fun a => (2:ℝ)^((θ a)⁻¹)) l (𝓝 (1:ℝ)) := by
    simpa only [Real.rpow_zero] using tendsto_const_nhds.rpow hi (Or.inl (by norm_num : (2:ℝ) ≠ 0))
  have hh : Tendsto (fun a => (θ a)^((θ a)⁻¹)) l (𝓝 (1:ℝ)) := by
    simpa only [one_div,Function.comp_def] using tendsto_rpow_div.comp ht
  have hc : Tendsto (fun a => (2*θ a)^((θ a)⁻¹)) l (𝓝 (1:ℝ)) := by
    have hm := h2.mul hh
    simp only [one_mul] at hm
    apply hm.congr'
    filter_upwards [] with a
    exact (Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by linarith [hθ a] : 0 ≤ θ a)).symm
  have hlo : Tendsto (fun a => 1-(2*θ a)^((θ a)⁻¹)*(1-(min u v:ℝ))) l (𝓝 (min u v:ℝ)) := by
    simpa using (hc.mul_const (1-(min u v:ℝ))).const_sub 1
  have he : (comonotonic 2).cdf ![u,v] = (min u v:ℝ) := by rw [cdf_comonotonic_two]; rfl
  rw [he]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · exact Eventually.of_forall fun a => nelsen21_cdf_lower_bound (θ a) (hθ a) u v
  · exact Eventually.of_forall fun a => le_min ((nelsen21 (θ a) (hθ a)).cdf_le_coord ![u,v] 0)
      ((nelsen21 (θ a) (hθ a)).cdf_le_coord ![u,v] 1)

theorem nelsen21_tendsto_parameter {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) {η : ℝ} (hη : 1 ≤ η) (ht : Tendsto θ l (𝓝 η)) (u v : I) :
    Tendsto (fun a => (nelsen21 (θ a) (hθ a)).cdf ![u,v]) l (𝓝 ((nelsen21 η hη).cdf ![u,v])) := by
  have hp : 0 < η := by linarith
  have hi : ContinuousAt (fun x : ℝ => x⁻¹) η := continuousAt_id.inv₀ hp.ne'
  have hroot (t : I) : ContinuousAt (fun x : ℝ => (1-(1-(t:ℝ))^x)^x⁻¹) η := by
    have hh : ContinuousAt (fun x : ℝ => (1-(t:ℝ))^x) η :=
      continuousAt_const.rpow continuousAt_id (Or.inr hp)
    exact (continuousAt_const.sub hh).rpow hi (Or.inr (inv_pos.mpr hp))
  have hinner : ContinuousAt (fun x : ℝ => max 0 ((1-(1-(u:ℝ))^x)^x⁻¹+(1-(1-(v:ℝ))^x)^x⁻¹-1)) η :=
    continuousAt_const.max (((hroot u).add (hroot v)).sub continuousAt_const)
  have hf : ContinuousAt (fun x : ℝ =>
      1-(1-(max 0 ((1-(1-(u:ℝ))^x)^x⁻¹+(1-(1-(v:ℝ))^x)^x⁻¹-1))^x)^x⁻¹) η :=
    continuousAt_const.sub ((continuousAt_const.sub
    (hinner.rpow continuousAt_id (Or.inr hp))).rpow hi (Or.inr (inv_pos.mpr hp)))
  have hh := hf.tendsto.comp ht
  simpa only [nelsen21_cdf_full,Function.comp_def] using hh

theorem nelsen21_tendsto_one {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ a, 1 ≤ θ a) (ht : Tendsto θ l (𝓝 1)) (u v : I) :
    Tendsto (fun a => (nelsen21 (θ a) (hθ a)).cdf ![u,v]) l (𝓝 (countermonotonic.cdf ![u,v])) := by
  simpa only [nelsen21_one] using nelsen21_tendsto_parameter θ hθ (by norm_num : (1:ℝ) ≤ 1) ht u v

end Verification
