import Verification.Nelsen17

open ProbabilityTheory Set Copula

namespace Verification

noncomputable def n21Core (θ t : ℝ) : ℝ := 1-(1-(1-t)^θ)^θ⁻¹
noncomputable def n21CorePrime (θ t : ℝ) : ℝ :=
  -(1-t)^(θ-1)*(1-(1-t)^θ)^(θ⁻¹-1)

theorem n21_inner_mem {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Icc 0 1) :
    1-(1-t)^θ ∈ Icc (0:ℝ) 1 := by
  have hpow := Real.rpow_le_one (by linarith [ht.2] : 0 ≤ 1-t) (by linarith [ht.1] : 1-t ≤ 1) hθ.le
  have hn := Real.rpow_nonneg (by linarith [ht.2] : 0 ≤ 1-t) θ
  constructor <;> linarith

theorem n21Core_mem {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Icc 0 1) :
    n21Core θ t ∈ Icc (0:ℝ) 1 := by
  have hi := n21_inner_mem hθ ht
  have hp := Real.rpow_le_one hi.1 hi.2 (inv_pos.mpr hθ).le
  have hn := Real.rpow_nonneg hi.1 θ⁻¹
  dsimp [n21Core]
  constructor <;> linarith

theorem n21Core_antitone {θ : ℝ} (hθ : 0 < θ) : AntitoneOn (n21Core θ) (Icc 0 1) := by
  intro s hs t ht hst
  apply sub_le_sub_left
  apply Real.rpow_le_rpow (n21_inner_mem hθ hs).1 _ (inv_pos.mpr hθ).le
  apply sub_le_sub_left
  exact Real.rpow_le_rpow (by linarith [ht.2]) (by linarith) hθ.le

theorem n21Core_involutive {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Icc 0 1) :
    n21Core θ (n21Core θ t) = t := by
  unfold n21Core
  rw [sub_sub_cancel, Real.rpow_inv_rpow (n21_inner_mem hθ ht).1 hθ.ne',
    sub_sub_cancel, Real.rpow_rpow_inv (by linarith [ht.2] : 0 ≤ 1-t) hθ.ne']
  ring

theorem n21Core_deriv {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (n21Core θ) (n21CorePrime θ t) t := by
  have hx : 0 < 1-t := by linarith [ht.2]
  have hb : 0 < 1-(1-t)^θ := sub_pos.mpr (Real.rpow_lt_one hx.le (by linarith [ht.1]) hθ)
  have hh := ((((((hasDerivAt_id t).const_sub 1).rpow_const (p := θ) (Or.inl hx.ne')).const_sub 1).rpow_const
    (p := θ⁻¹) (Or.inl hb.ne')).const_sub 1)
  convert hh using 1
  · rfl
  · dsimp [n21CorePrime]
    field_simp

theorem n21Core_deriv2 {θ t : ℝ} (hθ : 0 < θ) (ht : t ∈ Ioo 0 1) :
    HasDerivAt (n21CorePrime θ)
      ((θ-1)*(1-t)^(θ-2)*(1-(1-t)^θ)^(θ⁻¹-2)) t := by
  have hx : 0 < 1-t := by linarith [ht.2]
  have hb : 0 < 1-(1-t)^θ := sub_pos.mpr (Real.rpow_lt_one hx.le (by linarith [ht.1]) hθ)
  have hX := (hasDerivAt_id t).const_sub 1
  have hP := (hX.rpow_const (p := θ) (Or.inl hx.ne')).const_sub 1
  have hh := ((hX.rpow_const (p := θ-1) (Or.inl hx.ne')).neg).mul
    (hP.rpow_const (p := θ⁻¹-1) (Or.inl hb.ne'))
  have he : (1-t)^(θ-1) = (1-t)^(θ-2)*(1-t) := by
    rw [show θ-1 = (θ-2)+1 by ring,Real.rpow_add_one hx.ne']
  have he2 : (1-t)^θ = (1-t)^(θ-2)*(1-t)^2 := by
    calc
      _ = (1-t)^((θ-2)+2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx,Real.rpow_two]
  have he3 : (1-(1-t)^θ)^(θ⁻¹-1) = (1-(1-t)^θ)^(θ⁻¹-2)*(1-(1-t)^θ) := by
    rw [show θ⁻¹-1 = (θ⁻¹-2)+1 by ring,Real.rpow_add_one hb.ne']
  convert hh using 1
  · rfl
  · dsimp only [Pi.neg_apply,id_eq]
    rw [show θ-1-1 = θ-2 by ring,show θ⁻¹-1-1 = θ⁻¹-2 by ring,he,he3,he2]
    field_simp
    ring

theorem n21Core_continuous {θ : ℝ} (hθ : 0 < θ) : Continuous (n21Core θ) := by
  exact continuous_const.sub ((continuous_const.sub
    ((continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr hθ.le))).rpow_const
      (fun _ => Or.inr (inv_pos.mpr hθ).le))

theorem n21Core_convex {θ : ℝ} (hθ : 1 ≤ θ) : ConvexOn ℝ (Icc 0 1) (n21Core θ) := by
  have hp : 0 < θ := by linarith
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1)
  · exact (n21Core_continuous hp).continuousOn
  · intro t ht; exact (n21Core_deriv hp (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht; exact (n21Core_deriv2 hp (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0:ℝ) 1 := by simpa only [interior_Icc] using ht
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hθ) (Real.rpow_nonneg (by linarith [ht'.2]) _))
      (Real.rpow_nonneg (n21_inner_mem hp ⟨ht'.1.le,ht'.2.le⟩).1 _)

end Verification
