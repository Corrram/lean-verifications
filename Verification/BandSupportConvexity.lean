import Verification.BandSupport
import Mathlib.Analysis.Convex.Function

/-! # Convexity of the exact diagonal-band support -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem max_sq_jensen (x y a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hs : a+c=1) :
    max 0 (a*x+c*y)^2 ≤ a*(max 0 x)^2+c*(max 0 y)^2 := by
  let X := max 0 x
  let Y := max 0 y
  have hX : 0 ≤ X := le_max_left _ _
  have hY : 0 ≤ Y := le_max_left _ _
  have hsum : 0 ≤ a*X+c*Y := add_nonneg (mul_nonneg ha hX) (mul_nonneg hc hY)
  have hm : max 0 (a*x+c*y) ≤ a*X+c*Y := by
    apply max_le hsum
    exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
      (mul_le_mul_of_nonneg_left (le_max_right _ _) hc)
  have hm0 : 0 ≤ max 0 (a*x+c*y) := le_max_left _ _
  have hh : max 0 (a*x+c*y)^2 ≤ (a*X+c*Y)^2 := by nlinarith
  have hvar : 0 ≤ a*c*(X-Y)^2 := mul_nonneg (mul_nonneg ha hc) (sq_nonneg _)
  have he : a*X^2+c*Y^2-(a*X+c*Y)^2 = a*c*(X-Y)^2 := by
    have hc' : c=1-a := by linarith
    rw [hc']; ring
  change max 0 (a*x+c*y)^2 ≤ a*X^2+c*Y^2
  linarith

theorem bandLowerEdge_convex {b : ℝ} (hb : 0 < b) :
    ConvexOn ℝ univ (bandLowerEdge b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a c ha hc hs
  simp only [smul_eq_mul]
  have h := max_sq_jensen (1-b*x) (1-b*y) a c ha hc hs
  have he : a*(1-b*x)+c*(1-b*y) = 1-b*(a*x+c*y) := by nlinarith only [hs]
  rw [he] at h
  have hd := div_le_div_of_nonneg_right h (by positivity : 0 ≤ 2*b)
  unfold bandLowerEdge
  have hid : (a*x+c*y)-1/(2*b)+(a*max 0 (1-b*x)^2+c*max 0 (1-b*y)^2)/(2*b) =
      a*(x-1/(2*b)+max 0 (1-b*x)^2/(2*b))+c*(y-1/(2*b)+max 0 (1-b*y)^2/(2*b)) := by
    have hc' : c=1-a := by linarith
    rw [hc']; ring
  linarith only [hd, hid]

/-- The exact support in the real square is convex for every positive slope. -/
theorem bandSupport_convex {b : ℝ} (hb : 0 < b) : Convex ℝ (bandSupport b) := by
  intro x hx y hy a c ha hc hs
  rcases hx with ⟨hx,hxl,hxu⟩
  rcases hy with ⟨hy,hyl,hyu⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change a*x i+c*y i ∈ Icc (0 : ℝ) 1
    constructor
    · exact add_nonneg (mul_nonneg ha (hx i).1) (mul_nonneg hc (hy i).1)
    · have h := add_le_add (mul_le_mul_of_nonneg_left (hx i).2 ha)
        (mul_le_mul_of_nonneg_left (hy i).2 hc)
      nlinarith only [h,hs]
  · have h := (bandLowerEdge_convex hb).2 (mem_univ (x 0)) (mem_univ (y 0)) ha hc hs
    change bandLowerEdge b (a*x 0+c*y 0) ≤ a*x 1+c*y 1
    simp only [smul_eq_mul] at h
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hxl ha) (mul_le_mul_of_nonneg_left hyl hc))
  · have h := (bandLowerEdge_convex hb).2 (mem_univ (1-x 0)) (mem_univ (1-y 0)) ha hc hs
    simp only [smul_eq_mul] at h
    have he : a*(1-x 0)+c*(1-y 0) = 1-(a*x 0+c*y 0) := by nlinarith only [hs]
    rw [he] at h
    change a*x 1+c*y 1 ≤ 1-bandLowerEdge b (1-(a*x 0+c*y 0))
    have hbound := add_le_add (mul_le_mul_of_nonneg_left hxu ha) (mul_le_mul_of_nonneg_left hyu hc)
    nlinarith only [h, hbound, hs]

end Verification
