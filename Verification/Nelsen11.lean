import Verification.Nelsen10
import Mathlib.Analysis.Convex.Deriv

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

noncomputable def n11Square (t : ℝ) : ℝ := (2-Real.exp t)^2
noncomputable def n11Psi (t : ℝ) : ℝ := (max 0 (2-Real.exp t))^2

theorem n11Square_deriv (t : ℝ) :
    HasDerivAt n11Square (-2*Real.exp t*(2-Real.exp t)) t := by
  convert ((Real.hasDerivAt_exp t).const_sub 2).pow 2 using 1 <;> first | rfl | ring

theorem n11Square_deriv2 (t : ℝ) :
    HasDerivAt (fun x => -2*Real.exp x*(2-Real.exp x))
      (4*Real.exp t*(Real.exp t-1)) t := by
  convert ((Real.hasDerivAt_exp t).const_mul (-2)).mul
    ((Real.hasDerivAt_exp t).const_sub 2) using 1
  ring

theorem n11Square_convex : ConvexOn ℝ (Ici 0) n11Square := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t _; exact (n11Square_deriv t).continuousAt.continuousWithinAt
  · intro t _; exact (n11Square_deriv t).hasDerivWithinAt
  · intro t _; exact (n11Square_deriv2 t).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := (show 0 < t by simpa only [interior_Ici, mem_Ioi] using ht).le
    have he := Real.one_le_exp_iff.mpr ht0
    positivity

theorem n11Psi_clip (t : ℝ) : n11Psi t = n11Square (min t (Real.log 2)) := by
  have he : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  rcases le_total t (Real.log 2) with ht | ht
  · rw [min_eq_left ht]
    have hh := Real.exp_le_exp.mpr ht
    rw [he] at hh
    simp [n11Psi, n11Square, max_eq_right (by linarith : 0 ≤ 2-Real.exp t)]
  · rw [min_eq_right ht]
    have hh := Real.exp_le_exp.mpr ht
    rw [he] at hh
    simp [n11Psi, n11Square, he, max_eq_left (by linarith : 2-Real.exp t ≤ 0)]

theorem n11Psi_convex : ConvexOn ℝ (Ici 0) n11Psi := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  have hk : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  let X := min x (Real.log 2)
  let Y := min y (Real.log 2)
  let Z := min (a*x+b*y) (Real.log 2)
  have hX : 0 ≤ X := le_min hx hk
  have hY : 0 ≤ Y := le_min hy hk
  have hZ : a*X+b*Y ≤ Z := by
    apply le_min
    · exact add_le_add (mul_le_mul_of_nonneg_left (min_le_left _ _) ha)
        (mul_le_mul_of_nonneg_left (min_le_left _ _) hb)
    · have hh := add_le_add (mul_le_mul_of_nonneg_left (min_le_right x (Real.log 2)) ha)
        (mul_le_mul_of_nonneg_left (min_le_right y (Real.log 2)) hb)
      nlinarith
  have hZE : Real.exp Z ≤ 2 := by
    have hh := Real.exp_le_exp.mpr (min_le_right (a*x+b*y) (Real.log 2))
    exact hh.trans_eq (Real.exp_log (by norm_num))
  have hm : n11Square Z ≤ n11Square (a*X+b*Y) := by
    have he := Real.exp_le_exp.mpr hZ
    unfold n11Square
    nlinarith
  have hc := n11Square_convex.2 hX hY ha hb hab
  simp only [smul_eq_mul] at hc
  simp only [n11Psi_clip]
  exact hm.trans hc

noncomputable def nelsen11BaseGenerator : BivariateGenerator where
  toFun := n11Psi
  invFun u := Real.log (2-Real.sqrt (u:ℝ))
  nonneg t _ := sq_nonneg _
  antitone x _ y _ hxy := by
    have hh := max_le_max (le_refl (0:ℝ)) (sub_le_sub_left (Real.exp_le_exp.mpr hxy) 2)
    dsimp [n11Psi]
    nlinarith [le_max_left 0 (2-Real.exp x), le_max_left 0 (2-Real.exp y)]
  convex := n11Psi_convex
  inv_nonneg u _ := by
    apply Real.log_nonneg
    have hh : Real.sqrt (u:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr u.property.2
    linarith
  inv_antitone u v _ huv := by
    have hh : Real.sqrt (v:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr v.property.2
    apply Real.log_le_log (by linarith : 0 < 2-Real.sqrt (v:ℝ))
    exact sub_le_sub_left (Real.sqrt_le_sqrt (show (u:ℝ) ≤ v from huv)) 2
  inv_one := by norm_num
  right_inv u _ := by
    have hh : Real.sqrt (u:ℝ) ≤ 1 := (Real.sqrt_le_one).mpr u.property.2
    dsimp [n11Psi]
    rw [Real.exp_log (by linarith : 0 < 2-Real.sqrt (u:ℝ))]
    simp only [sub_sub_cancel, max_eq_right (Real.sqrt_nonneg _), Real.sq_sqrt u.property.1]

noncomputable def nelsen11Positive (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1/2) : Copula 2 :=
  (nelsen11BaseGenerator.innerPower (2*θ)⁻¹
    ((one_le_inv₀ (by positivity)).mpr (by linarith))).copula

noncomputable def nelsen11 (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) : Copula 2 :=
  if h : θ = 0 then independence 2
  else nelsen11Positive θ (lt_of_le_of_ne hθ0 (Ne.symm h)) hθ1

theorem nelsen11_zero : nelsen11 0 le_rfl (by norm_num) = independence 2 := by
  simp [nelsen11]

theorem nelsen11Base_cdf (u v : I) :
    nelsen11BaseGenerator.copula.cdf ![u,v] =
      (max 0 (2-(2-Real.sqrt (u:ℝ))*(2-Real.sqrt (v:ℝ))))^2 := by
  have hu1 : Real.sqrt (u:ℝ) ≤ 1 := Real.sqrt_le_one.mpr u.property.2
  have hv1 : Real.sqrt (v:ℝ) ≤ 1 := Real.sqrt_le_one.mpr v.property.2
  rw [BivariateGenerator.cdf_copula]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, BivariateGenerator.cdf]
  by_cases hu : u = 0
  · subst u
    norm_num
    rw [max_eq_left (by nlinarith : 2-2*(2-Real.sqrt (v:ℝ)) ≤ 0)]
    norm_num
  by_cases hv : v = 0
  · subst v
    norm_num
    rw [max_eq_left (by nlinarith : 2-(2-Real.sqrt (u:ℝ))*2 ≤ 0)]
    norm_num
  simp only [hu, hv, or_self, ite_false]
  change (max 0 (2-Real.exp (Real.log (2-Real.sqrt (u:ℝ))+
    Real.log (2-Real.sqrt (v:ℝ)))))^2 = _
  rw [Real.exp_add, Real.exp_log (by linarith : 0 < 2-Real.sqrt (u:ℝ)),
    Real.exp_log (by linarith : 0 < 2-Real.sqrt (v:ℝ))]

theorem nelsen11_positive_cdf (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1/2) (u v : I) :
    (nelsen11Positive θ hθ hθ1).cdf ![u,v] =
      (max 0 ((u:ℝ)^θ*(v:ℝ)^θ-2*(1-(u:ℝ)^θ)*(1-(v:ℝ)^θ)))^θ⁻¹ := by
  unfold nelsen11Positive
  rw [innerPower_cdf, nelsen11Base_cdf]
  simp only [coe_unitPower, inv_inv]
  have hs (w : I) : Real.sqrt ((w:ℝ)^(2*θ)) = (w:ℝ)^θ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul w.property.1]
    congr 1
    ring
  rw [hs u, hs v, ← Real.rpow_natCast_mul (le_max_left 0 _) 2]
  norm_num only [Nat.cast_ofNat]
  have hp : (2:ℝ)*(2*θ)⁻¹ = θ⁻¹ := by field_simp
  rw [hp]
  congr 2
  ring

theorem nelsen11_cdf (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1/2) (u v : I) :
    (nelsen11 θ hθ.le hθ1).cdf ![u,v] =
      (max 0 ((u:ℝ)^θ*(v:ℝ)^θ-2*(1-(u:ℝ)^θ)*(1-(v:ℝ)^θ)))^θ⁻¹ := by
  simp only [nelsen11, hθ.ne', dite_false]
  exact nelsen11_positive_cdf θ hθ hθ1 u v

theorem nelsen11_isNQD (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (nelsen11 θ hθ0 hθ1).IsNQD := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen11_zero]
    exact isNQD_independence
  have hp : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hz)
  intro u v
  rw [nelsen11_cdf θ hp hθ1]
  have hu := Real.rpow_le_one u.property.1 u.property.2 hθ0
  have hv := Real.rpow_le_one v.property.1 v.property.2 hθ0
  have hu0 := Real.rpow_nonneg u.property.1 θ
  have hv0 := Real.rpow_nonneg v.property.1 θ
  have hb : max 0 ((u:ℝ)^θ*(v:ℝ)^θ-2*(1-(u:ℝ)^θ)*(1-(v:ℝ)^θ)) ≤ (u:ℝ)^θ*(v:ℝ)^θ := by
    apply max_le (mul_nonneg hu0 hv0)
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)]
  have hh := Real.rpow_le_rpow (le_max_left 0 _) hb (inv_nonneg.mpr hθ0)
  simpa only [Real.mul_rpow hu0 hv0, Real.rpow_rpow_inv u.property.1 hz,
    Real.rpow_rpow_inv v.property.1 hz] using hh

theorem nelsen11_isPQD_iff (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (nelsen11 θ hθ0 hθ1).IsPQD ↔ θ = 0 := by
  constructor
  · intro h
    by_contra hz
    have hp : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hz)
    let q : I := unitPower ⟨1/2, by norm_num, by norm_num⟩ θ⁻¹ (inv_nonneg.mpr hθ0)
    have hq : (q:ℝ)^θ = 1/2 := by
      exact Real.rpow_inv_rpow (by norm_num) hz
    have hqpos : 0 < (q:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hh := h q q
    rw [nelsen11_cdf θ hp hθ1, hq] at hh
    norm_num [Real.zero_rpow (inv_ne_zero hz)] at hh
    nlinarith [mul_pos hqpos hqpos]
  · rintro rfl
    rw [nelsen11_zero]
    exact isPQD_independence

theorem nelsen11_isCI_iff (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (nelsen11 θ hθ0 hθ1).IsCI ↔ θ = 0 := by
  constructor
  · intro h
    exact (nelsen11_isPQD_iff θ hθ0 hθ1).mp h.isPQD
  · rintro rfl
    rw [nelsen11_zero]
    exact isCI_independence

theorem nelsen11_density_tp2_iff (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (nelsen11 θ hθ0 hθ1).HasMTP2Density ↔ θ = 0 := by
  constructor
  · intro h
    exact (nelsen11_isPQD_iff θ hθ0 hθ1).mp (hasMTP2Density_isPQD _ h)
  · rintro rfl
    rw [nelsen11_zero]
    exact hasMTP2Density_independence 2

theorem nelsen11_tails (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (nelsen11 θ hθ0 hθ1).HasLowerTailDependence 0 ∧
      (nelsen11 θ hθ0 hθ1).HasUpperTailDependence 0 :=
  ⟨isNQD_hasLowerTailDependence_zero (nelsen11_isNQD θ hθ0 hθ1),
    isNQD_hasUpperTailDependence_zero (nelsen11_isNQD θ hθ0 hθ1)⟩

end Verification
