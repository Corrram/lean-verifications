import Verification.Nelsen16
import Copula.Order.Orthant

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n16Root (a k θ : ℝ) : ℝ :=
  (a-θ*k+Real.sqrt ((a-θ*k)^2+4*θ))/2

theorem n16Root_properties {a k θ : ℝ} (hθ : 0 ≤ θ) :
    0 ≤ n16Root a k θ ∧
    (n16Root a k θ)^2-(a-θ*k)*n16Root a k θ-θ = 0 ∧
    0 ≤ 2*n16Root a k θ-(a-θ*k) := by
  have hs := Real.sq_sqrt (show 0 ≤ (a-θ*k)^2+4*θ by nlinarith [sq_nonneg (a-θ*k)])
  have hp := Real.sqrt_nonneg ((a-θ*k)^2+4*θ)
  dsimp [n16Root]
  constructor
  · have hh : 0 ≤ a-θ*k+Real.sqrt ((a-θ*k)^2+4*θ) := by nlinarith
    linarith
  constructor <;> nlinarith

theorem n16Root_bound {a k θ : ℝ} (hθ : 0 ≤ θ) (hk : 0 < k) (ha : a*k ≤ 1) :
    k*n16Root a k θ ≤ 1 := by
  obtain ⟨hc,he,_⟩ := n16Root_properties (a := a) (k := k) hθ
  by_contra hh
  have hx : 1 < k*n16Root a k θ := lt_of_not_ge hh
  have hp : 0 < n16Root a k θ := by nlinarith
  have hd : a < n16Root a k θ := by nlinarith
  have hprod := mul_pos hp (sub_pos.mpr hd)
  have hparam := mul_nonneg hθ (show 0 ≤ k*n16Root a k θ-1 by linarith)
  nlinarith

theorem n16Root_monotone {a k θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ ≤ η)
    (hk : 0 < k) (ha : a*k ≤ 1) : n16Root a k θ ≤ n16Root a k η := by
  have hη : 0 ≤ η := hθ.trans hθη
  obtain ⟨hc,he,_⟩ := n16Root_properties (a := a) (k := k) hθ
  obtain ⟨hd,hf,hs⟩ := n16Root_properties (a := a) (k := k) hη
  have hb := n16Root_bound hθ hk ha
  have hprod := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hθη)
    (show k*n16Root a k θ-1 ≤ 0 by linarith)
  have hq : (n16Root a k θ)^2-(a-η*k)*n16Root a k θ-η ≤ 0 := by nlinarith
  by_contra hh
  have hcd : n16Root a k η < n16Root a k θ := lt_of_not_ge hh
  have hsum : 0 < n16Root a k θ+n16Root a k η-(a-η*k) := by linarith
  have hh' := mul_pos (sub_pos.mpr hcd) hsum
  nlinarith

theorem n16_inverse_sum_pos {u v : I} (hu : 0 < (u:ℝ)) (hv : 0 < (v:ℝ)) :
    0 < (u:ℝ)⁻¹+(v:ℝ)⁻¹-1 := by
  have h₁ := one_div_le_one_div_of_le hu u.property.2
  have h₂ := one_div_le_one_div_of_le hv v.property.2
  simp only [one_div, inv_one] at h₁ h₂
  linarith

theorem n16_sum_bound {u v : I} (hu : 0 < (u:ℝ)) (hv : 0 < (v:ℝ)) :
    ((u:ℝ)+(v:ℝ)-1)*((u:ℝ)⁻¹+(v:ℝ)⁻¹-1) ≤ 1 := by
  have he : 1-((u:ℝ)+(v:ℝ)-1)*((u:ℝ)⁻¹+(v:ℝ)⁻¹-1) =
      (1-(u:ℝ))*(1-(v:ℝ))*((u:ℝ)+(v:ℝ))/((u:ℝ)*(v:ℝ)) := by field_simp; ring
  have hn : 0 ≤ (1-(u:ℝ))*(1-(v:ℝ))*((u:ℝ)+(v:ℝ))/((u:ℝ)*(v:ℝ)) :=
    div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr v.property.2))
      (add_nonneg hu.le hv.le)) (mul_nonneg hu.le hv.le)
  linarith

theorem nelsen16_lowerOrthant_monotone {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (nelsen16 θ hθ).LowerOrthantLE (nelsen16 η hη) := by
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, nelsen16_cdf_full, nelsen16_cdf_full]
  split_ifs with hz
  · rfl
  have hu : 0 < (x 0:ℝ) := lt_of_le_of_ne (x 0).property.1
    (Ne.symm (fun h => hz (Or.inl (Subtype.ext h))))
  have hv : 0 < (x 1:ℝ) := lt_of_le_of_ne (x 1).property.1
    (Ne.symm (fun h => hz (Or.inr (Subtype.ext h))))
  exact n16Root_monotone hθ hθη (n16_inverse_sum_pos hu hv) (n16_sum_bound hu hv)

theorem n16Root_scaled_lower {a k θ : ℝ} (hθ : 0 < θ) (hk : 1 ≤ k)
    (ha : a*k ≤ 1) (ha0 : -1 ≤ a) : 1-2/θ ≤ k*n16Root a k θ := by
  obtain ⟨hc,he,_⟩ := n16Root_properties (a := a) (k := k) hθ.le
  have hb := n16Root_bound hθ.le (by linarith : 0 < k) ha
  have hc1 : n16Root a k θ ≤ 1 := by nlinarith
  have hs : (n16Root a k θ)^2 ≤ 1 := by nlinarith
  have hm := mul_nonneg hc (show 0 ≤ a+1 by linarith)
  have hq : θ*(1-k*n16Root a k θ) ≤ 2 := by nlinarith
  have hd : 1-k*n16Root a k θ ≤ 2/θ := (le_div_iff₀ hθ).mpr (by nlinarith)
  linarith

theorem n16Root_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Filter.Tendsto θ l Filter.atTop)
    {a k : ℝ} (hk : 1 ≤ k) (ha : a*k ≤ 1) (ha0 : -1 ≤ a) :
    Filter.Tendsto (fun z => n16Root a k (θ z)) l (nhds k⁻¹) := by
  have hi : Filter.Tendsto (fun z => (2:ℝ)/θ z) l (nhds 0) := Filter.Tendsto.div_atTop tendsto_const_nhds hlim
  have hlo : Filter.Tendsto (fun z => 1-2/θ z) l (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hi
  have hh : Filter.Tendsto (fun z => k*n16Root a k (θ z)) l (nhds 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
    · filter_upwards [hlim.eventually (Filter.eventually_gt_atTop 0)] with z hz
      exact n16Root_scaled_lower hz hk ha ha0
    · exact Filter.Eventually.of_forall (fun z => n16Root_bound (hθ z) (by linarith) ha)
  have he (z : α) : k*n16Root a k (θ z)/k = n16Root a k (θ z) := by
    have hk0 : k ≠ 0 := ne_of_gt (by linarith : 0 < k)
    field_simp
  simpa only [he, one_div] using hh.div_const k

theorem nelsen16_tendsto_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 ≤ θ z) (hlim : Filter.Tendsto θ l Filter.atTop) (u v : I) :
    Filter.Tendsto (fun z => (nelsen16 (θ z) (hθ z)).cdf ![u,v]) l
      (nhds ((clayton 2 1 (by norm_num)).cdf ![u,v])) := by
  by_cases hu : u = 0
  · subst u; simp; exact tendsto_const_nhds
  by_cases hv : v = 0
  · subst v
    have hz (C : Copula 2) : C.cdf ![u,0] = 0 := C.cdf_eq_zero_of_coord_eq_zero _ 1 (by simp)
    simp only [hz]; exact tendsto_const_nhds
  have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hq : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have hk : 1 ≤ (u:ℝ)⁻¹+(v:ℝ)⁻¹-1 := by
    have h₁ := one_div_le_one_div_of_le hp u.property.2
    have h₂ := one_div_le_one_div_of_le hq v.property.2
    simp only [one_div, inv_one] at h₁ h₂
    linarith
  have hh := n16Root_tendsto_atTop θ hθ hlim hk (n16_sum_bound hp hq)
    (show -1 ≤ (u:ℝ)+(v:ℝ)-1 by linarith)
  have hc : (clayton 2 1 (by norm_num)).cdf ![u,v] = ((u:ℝ)⁻¹+(v:ℝ)⁻¹-1)⁻¹ := by
    rw [cdf_clayton_of_pos 1 (by norm_num) ![u,v]
      (by intro i; fin_cases i; exact hp; exact hq)]
    simp [Fin.sum_univ_two, Real.rpow_neg_one]
    ring
  simpa only [nelsen16_cdf_full, hu, hv, or_self, ite_false, hc, n16Root] using hh

end Verification
