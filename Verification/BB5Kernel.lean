import Verification.ClaytonScaledTail
import Mathlib.Analysis.MeanInequalitiesPow

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem galambosTailKernel_pos (δ x y : ℝ) (hx : 0<x) (hy : 0<y) :
    0<galambosTailKernel δ x y :=
  Real.rpow_pos_of_pos (add_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)) _

theorem galambosTailKernel_le_min (δ : ℝ) (hδ : 0<δ) (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    galambosTailKernel δ x y ≤ min x y := by
  have hn : -1/δ≤0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hδ.le
  have h1 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx (-δ))
    (le_add_of_nonneg_right (Real.rpow_nonneg hy.le (-δ))) hn
  have h2 := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hy (-δ))
    (le_add_of_nonneg_left (Real.rpow_nonneg hx.le (-δ))) hn
  rw [← Real.rpow_mul hx.le,show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one] at h1
  rw [← Real.rpow_mul hy.le,show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one] at h2
  exact le_min h1 h2

/-- The BB5 logarithmic exponent on strictly positive coordinates.
The copula construction and the boundary extension are separate obligations. -/
noncomputable def bb5TailKernel (θ δ x y : ℝ) : ℝ :=
  (x^θ+y^θ-galambosTailKernel δ (x^θ) (y^θ))^(1/θ)

theorem bb5TailKernel_inner_pos (θ δ x y : ℝ) (hδ : 0<δ) (hx : 0<x) (hy : 0<y) :
    0<x^θ+y^θ-galambosTailKernel δ (x^θ) (y^θ) := by
  have h := galambosTailKernel_le_min δ hδ (x^θ) (y^θ)
    (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)
  have hh := h.trans (min_le_left _ _)
  linarith [Real.rpow_pos_of_pos hy θ]

theorem bb5TailKernel_bounds (θ δ x y : ℝ) (hθ : 1≤θ) (hδ : 0<δ) (hx : 0<x) (hy : 0<y) :
    max x y ≤ bb5TailKernel θ δ x y ∧ bb5TailKernel θ δ x y ≤ x+y := by
  have ht : 0<θ := by linarith
  have hk := galambosTailKernel_le_min δ hδ (x^θ) (y^θ)
    (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)
  have hi := bb5TailKernel_inner_pos θ δ x y hδ hx hy
  have hpow (z : ℝ) (hz : 0≤z) : (z^θ)^(1/θ)=z := by
    rw [one_div,Real.rpow_rpow_inv hz ht.ne']
  constructor
  · apply max_le
    · have hh := Real.rpow_le_rpow (Real.rpow_nonneg hx.le θ)
        (show x^θ≤x^θ+y^θ-galambosTailKernel δ (x^θ) (y^θ) by linarith [hk.trans (min_le_right _ _)])
        (one_div_nonneg.mpr ht.le)
      rw [hpow x hx.le] at hh
      exact hh
    · have hh := Real.rpow_le_rpow (Real.rpow_nonneg hy.le θ)
        (show y^θ≤x^θ+y^θ-galambosTailKernel δ (x^θ) (y^θ) by linarith [hk.trans (min_le_left _ _)])
        (one_div_nonneg.mpr ht.le)
      rw [hpow y hy.le] at hh
      exact hh
  · have hh := Real.rpow_le_rpow hi.le
      (show x^θ+y^θ-galambosTailKernel δ (x^θ) (y^θ)≤x^θ+y^θ by
        linarith [galambosTailKernel_pos δ (x^θ) (y^θ) (Real.rpow_pos_of_pos hx θ) (Real.rpow_pos_of_pos hy θ)])
      (one_div_nonneg.mpr ht.le)
    exact hh.trans (Real.rpow_add_rpow_le_add hx.le hy.le hθ)

theorem bb5TailKernel_shape_one (δ x y : ℝ) :
    bb5TailKernel 1 δ x y=x+y-galambosTailKernel δ x y := by
  simp [bb5TailKernel]

theorem galambosTailKernel_homogeneous (δ : ℝ) (hδ : 0<δ) (c x y : ℝ)
    (hc : 0<c) (hx : 0≤x) (hy : 0≤y) :
    galambosTailKernel δ (c*x) (c*y)=c*galambosTailKernel δ x y := by
  unfold galambosTailKernel
  rw [Real.mul_rpow hc.le hx,Real.mul_rpow hc.le hy,← mul_add,
    Real.mul_rpow (Real.rpow_nonneg hc.le _) (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)),
    ← Real.rpow_mul hc.le,show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one]

theorem bb5TailKernel_homogeneous (θ δ c x y : ℝ) (hθ : 1≤θ) (hδ : 0<δ)
    (hc : 0<c) (hx : 0<x) (hy : 0<y) :
    bb5TailKernel θ δ (c*x) (c*y)=c*bb5TailKernel θ δ x y := by
  unfold bb5TailKernel
  rw [Real.mul_rpow hc.le hx.le,Real.mul_rpow hc.le hy.le,
    galambosTailKernel_homogeneous δ hδ (c^θ) _ _ (Real.rpow_pos_of_pos hc _)
      (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hy.le _),← mul_add,← mul_sub,
    Real.mul_rpow (Real.rpow_nonneg hc.le _) (bb5TailKernel_inner_pos θ δ x y hδ hx hy).le,
    one_div,Real.rpow_rpow_inv hc.le (by linarith : θ≠0)]

theorem bb5TailKernel_formula (θ δ x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    bb5TailKernel θ δ x y=(x^θ+y^θ-(x^(-δ*θ)+y^(-δ*θ))^(-1/δ))^(1/θ) := by
  unfold bb5TailKernel galambosTailKernel
  rw [← Real.rpow_mul hx,← Real.rpow_mul hy,mul_comm θ (-δ)]

end Verification
