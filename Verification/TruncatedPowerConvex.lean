import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set

namespace Verification

theorem convexOn_clip_left {f : ℝ → ℝ} {c : ℝ}
    (hc : ConvexOn ℝ (Ici c) f) (hm : MonotoneOn f (Ici c)) :
    ConvexOn ℝ univ (fun x => f (max c x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  have hxy : c ≤ a*max c x+b*max c y := by
    have hh := add_le_add (mul_le_mul_of_nonneg_left (le_max_left c x) ha)
      (mul_le_mul_of_nonneg_left (le_max_left c y) hb)
    simpa only [← add_mul, hab, one_mul] using hh
  have hz : max c (a*x+b*y) ≤ a*max c x+b*max c y := by
    refine max_le hxy ?_
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right c x) ha)
      (mul_le_mul_of_nonneg_left (le_max_right c y) hb)
  exact (hm (le_max_left c _) hxy hz).trans (hc.2 (le_max_left c x) (le_max_left c y) ha hb hab)

noncomputable def powerCut (θ a k : ℝ) : ℝ := (a/k)^θ⁻¹
noncomputable def powerBranch (θ a k x : ℝ) : ℝ := (k*x^θ-a)^θ⁻¹

theorem powerCut_nonneg {a k : ℝ} (ha : 0 ≤ a) (hk : 0 < k) (θ : ℝ) :
    0 ≤ powerCut θ a k := Real.rpow_nonneg (div_nonneg ha hk.le) _

theorem powerCut_pow {θ a k : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hk : 0 < k) :
    (powerCut θ a k)^θ = a/k := Real.rpow_inv_rpow (div_nonneg ha hk.le) hθ.ne'

theorem powerBranch_base_pos {θ a k x : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hk : 0 < k)
    (hx : powerCut θ a k < x) : 0 < k*x^θ-a := by
  have hh := Real.rpow_lt_rpow (powerCut_nonneg ha hk θ) hx hθ
  rw [powerCut_pow hθ ha hk] at hh
  have h := (div_lt_iff₀ hk).mp hh
  nlinarith

theorem powerBranch_deriv {θ a k x : ℝ} (hθ : 0 < θ) (ha : 0 ≤ a) (hk : 0 < k)
    (hx : powerCut θ a k < x) :
    HasDerivAt (powerBranch θ a k) (k*(k-a/x^θ)^(θ⁻¹-1)) x := by
  have hx0 : 0 < x := lt_of_le_of_lt (powerCut_nonneg ha hk θ) hx
  have hb := powerBranch_base_pos hθ ha hk hx
  have hxp : 0 < x^θ := Real.rpow_pos_of_pos hx0 _
  have hd : 0 < k-a/x^θ := by
    have hh := (div_lt_iff₀ hxp).mpr (by nlinarith : a < k*x^θ)
    linarith
  have hp := (hasDerivAt_id x).rpow_const (p := θ) (Or.inl hx0.ne')
  have hf := ((hp.const_mul k).sub_const a).rpow_const (p := θ⁻¹) (Or.inl hb.ne')
  convert hf using 1
  · rfl
  · dsimp
    have he : k*x^θ-a = x^θ*(k-a/x^θ) := by field_simp
    rw [he, Real.mul_rpow hxp.le hd.le, ← Real.rpow_mul hx0.le]
    have he' : θ*(θ⁻¹-1) = 1-θ := by field_simp
    rw [he']
    have hm : x^(θ-1)*x^(1-θ) = 1 := by rw [← Real.rpow_add hx0]; simp
    have ht : θ*θ⁻¹ = 1 := mul_inv_cancel₀ hθ.ne'
    calc
      _ = k*(k-a/x^θ)^(θ⁻¹-1)*(θ*θ⁻¹)*(x^(θ-1)*x^(1-θ)) := by rw [ht,hm]; ring
      _ = _ := by ring

theorem powerBranch_convex {θ a k : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hk : 0 < k) : ConvexOn ℝ (Ici (powerCut θ a k)) (powerBranch θ a k) := by
  have hc : Continuous (powerBranch θ a k) := by
    unfold powerBranch
    exact ((continuous_const.mul (Real.continuous_rpow_const hθ.le)).sub continuous_const).rpow_const
      (fun _ => Or.inr (inv_nonneg.mpr hθ.le))
  apply MonotoneOn.convexOn_of_deriv (convex_Ici _) hc.continuousOn
  · intro x hx
    have hx' : powerCut θ a k < x := by simpa only [interior_Ici, mem_Ioi] using hx
    exact (powerBranch_deriv hθ ha hk hx').differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx' : powerCut θ a k < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hy' : powerCut θ a k < y := by simpa only [interior_Ici, mem_Ioi] using hy
    rw [(powerBranch_deriv hθ ha hk hx').deriv, (powerBranch_deriv hθ ha hk hy').deriv]
    apply mul_le_mul_of_nonneg_left _ hk.le
    have hx0 : 0 < x := lt_of_le_of_lt (powerCut_nonneg ha hk θ) hx'
    have hxp : 0 < x^θ := Real.rpow_pos_of_pos hx0 _
    have hb := powerBranch_base_pos hθ ha hk hx'
    have hd : 0 ≤ k-a/x^θ := by
      have hh := (div_le_iff₀ hxp).mpr (by linarith : a ≤ k*x^θ)
      linarith
    apply Real.rpow_le_rpow hd
    · exact sub_le_sub_left (div_le_div_of_nonneg_left ha hxp (Real.rpow_le_rpow hx0.le hxy hθ.le)) k
    · have hh := (one_le_inv₀ hθ).mpr hθ1
      linarith

theorem truncatedPower_convex {θ a k : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hk : 0 < k) :
    ConvexOn ℝ (Ici 0) (fun x => (max 0 (k*x^θ-a))^θ⁻¹) := by
  have hm : MonotoneOn (powerBranch θ a k) (Ici (powerCut θ a k)) := by
    intro x hx y _ hxy
    have hx0 : 0 ≤ x := le_trans (powerCut_nonneg ha hk θ) hx
    have hbase : 0 ≤ k*x^θ-a := by
      have hh := Real.rpow_le_rpow (powerCut_nonneg ha hk θ) hx hθ.le
      rw [powerCut_pow hθ ha hk] at hh
      have hp := (div_le_iff₀ hk).mp hh
      nlinarith
    apply Real.rpow_le_rpow hbase
    · exact sub_le_sub_right (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0 hxy hθ.le) hk.le) a
    · exact inv_nonneg.mpr hθ.le
  have hc := (convexOn_clip_left (powerBranch_convex hθ hθ1 ha hk) hm).subset
    (subset_univ (Ici (0:ℝ))) (convex_Ici 0)
  have he (x : ℝ) (hx : x ∈ Ici (0:ℝ)) :
      powerBranch θ a k (max (powerCut θ a k) x) = (max 0 (k*x^θ-a))^θ⁻¹ := by
    rcases le_total x (powerCut θ a k) with h | h
    · have hh := Real.rpow_le_rpow hx h hθ.le
      rw [powerCut_pow hθ ha hk] at hh
      have hp := (le_div_iff₀ hk).mp hh
      have hb : k*x^θ-a ≤ 0 := by nlinarith
      rw [max_eq_left h, max_eq_left hb]
      unfold powerBranch
      rw [powerCut_pow hθ ha hk]
      have hz : k*(a/k)-a = 0 := by field_simp; ring
      rw [hz]
    · have hh := Real.rpow_le_rpow (powerCut_nonneg ha hk θ) h hθ.le
      rw [powerCut_pow hθ ha hk] at hh
      have hp := (div_le_iff₀ hk).mp hh
      have hb : 0 ≤ k*x^θ-a := by nlinarith
      rw [max_eq_right h, max_eq_right hb]
      rfl
  exact hc.congr he

end Verification
