import Verification.ForwardGraphUniqueness
import Copula.Rank.Region.RhoFootrule.UpperLipschitz
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Contact rigidity of a Lipschitz dual potential -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval NNReal Topology

namespace Verification

/-- A globally feasible dual potential is strictly negative when its Lipschitz
constant is smaller than the distance coefficient. This excludes diagonal contact. -/
theorem dual_potential_negative (g : ℝ → ℝ) (v : ℝ≥0) (θ : ℝ)
    (hg : LipschitzWith v g) (hθ : (v : ℝ) < θ)
    (hf : ∀ a b : ℝ, g a + g b ≤ (b-a)^2 - θ * |b-a|) (a : ℝ) : g a < 0 := by
  let r := (θ - v) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hl := hg.dist_le_mul a (a+r)
  rw [Real.dist_eq, Real.dist_eq, show a-(a+r) = -r by ring,
    abs_neg, abs_of_pos hr] at hl
  have hl' := (abs_le.mp hl).2
  have hh := hf a (a+r)
  rw [show a+r-a = r by ring, abs_of_pos hr] at hh
  have hrid : 2*r = θ-v := by dsimp [r]; ring
  nlinarith [sq_pos_of_pos hr]

/-- At a differentiability point, the dual contact above the diagonal has one
possible endpoint. No explicit case split over the spline pieces is needed. -/
theorem dual_upper_contact (g : ℝ → ℝ) (θ a b : ℝ)
    (hf : ∀ x y : ℝ, g x + g y ≤ (y-x)^2 - θ * |y-x|)
    (hab : a < b) (hd : DifferentiableAt ℝ g a)
    (he : g a + g b = (b-a)^2 - θ * |b-a|) :
    b = a + (θ - deriv g a) / 2 := by
  let f := fun x : ℝ => (b-x)^2 - θ*(b-x) - g x - g b
  have hf0 : f a = 0 := by
    dsimp [f]
    rw [abs_of_pos (sub_pos.mpr hab)] at he
    linarith
  have hmin : IsLocalMin f a := by
    apply IsMinOn.isLocalMin (s := Iio b) _ (Iio_mem_nhds hab)
    intro x hx
    rw [hf0]
    have hh := hf x b
    rw [abs_of_pos (sub_pos.mpr hx)] at hh
    dsimp [f]
    linarith
  have hd' : HasDerivAt f (-2*(b-a) + θ - deriv g a) a := by
    convert! ((((hasDerivAt_const a b).sub (hasDerivAt_id a)).pow 2).sub
      (((hasDerivAt_const a b).sub (hasDerivAt_id a)).const_mul θ)).sub
      hd.hasDerivAt |>.sub_const (g b) using 1
    dsimp [f, id_eq]
    ring
  have hh := hmin.hasDerivAt_eq_zero hd'
  linarith

end Verification
