import Verification.LaplaceJointDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The Laplace radial integral is a modified Bessel function

`K₀(z)=∫₀^∞ exp(-z cosh s) ds` (the standard integral representation, `z>0`). For `q>0`
the substitution `t=√(q/2)·e^s` turns `∫₀^∞ t⁻¹ exp(-t-q/(2t)) dt` into
`∫_ℝ exp(-√(2q) cosh s) ds = 2K₀(√(2q))`. Hence the Laplace joint density
`(2π√(1-r²))⁻¹ · laplaceRadialDensity(Q)` equals the printed `K₀(√(2Q))/(π√(1-r²))`.
-/

open MeasureTheory Real Set
open scoped ENNReal

namespace Verification

/-- The modified Bessel function of the second kind of order zero, in its integral form. -/
noncomputable def besselK0 (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal (exp (-z * cosh s))

theorem lintegral_Iio_eq_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ s in Iio (0:ℝ), f s = ∫⁻ s in Ioi (0:ℝ), f (-s) := by
  have himg : (fun x : ℝ => -x) '' Ioi 0 = Iio 0 := by
    ext y; simp only [mem_image, mem_Ioi, mem_Iio]
    constructor
    · rintro ⟨x, hx, rfl⟩; linarith
    · intro hy; exact ⟨-y, by linarith, by ring⟩
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Ioi (0:ℝ)) (f := fun x => -x)
    (f' := fun _ => -1) measurableSet_Ioi
    (fun x _ => (hasDerivAt_neg x).hasDerivWithinAt) (neg_injective.injOn) f
  rw [himg] at h
  rw [h]
  simp

theorem lintegral_even (f : ℝ → ℝ≥0∞) (hf : ∀ s, f (-s) = f s) :
    ∫⁻ s, f s = 2 * ∫⁻ s in Ioi (0:ℝ), f s := by
  have hu : (univ : Set ℝ) = Iio 0 ∪ Ici 0 := by
    ext x; simp only [mem_univ, mem_union, mem_Iio, mem_Ici, true_iff]; exact lt_or_ge x 0
  have hdis : Disjoint (Iio (0:ℝ)) (Ici 0) :=
    disjoint_left.mpr fun x (hx : x < 0) (hx' : 0 ≤ x) => absurd hx' (not_le.mpr hx)
  rw [← setLIntegral_univ, hu, lintegral_union measurableSet_Ici hdis, lintegral_Iio_eq_Ioi,
    setLIntegral_congr Ioi_ae_eq_Ici.symm]
  simp only [hf]
  ring

theorem laplaceRadialDensity_eq_besselK0 {q : ℝ} (hq : 0 < q) :
    laplaceRadialDensity q = 2 * besselK0 (Real.sqrt (2 * q)) := by
  set c := Real.sqrt (q / 2)
  have hc : 0 < c := Real.sqrt_pos.mpr (by positivity)
  have hc2 : c ^ 2 = q / 2 := Real.sq_sqrt (by positivity)
  have h2c : 2 * c = Real.sqrt (2 * q) := by
    rw [show 2 * q = 2 ^ 2 * (q / 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
  have himg : (fun s : ℝ => c * exp s) '' univ = Ioi 0 := by
    ext t; simp only [image_univ, mem_range, mem_Ioi]
    constructor
    · rintro ⟨s, rfl⟩; positivity
    · intro ht; exact ⟨log (t / c), by rw [exp_log (div_pos ht hc)]; field_simp⟩
  have hinj : InjOn (fun s : ℝ => c * exp s) univ := fun a _ b _ h => by
    have : exp a = exp b := mul_left_cancel₀ hc.ne' h
    exact exp_injective this
  have hcv := lintegral_image_eq_lintegral_abs_deriv_mul (s := univ)
    (f := fun s : ℝ => c * exp s) (f' := fun s => c * exp s) MeasurableSet.univ
    (fun x _ => ((hasDerivAt_exp x).const_mul c).hasDerivWithinAt) hinj
    (fun t => ENNReal.ofReal (t⁻¹ * exp (-t - q / (2 * t))))
  rw [himg, setLIntegral_univ] at hcv
  unfold laplaceRadialDensity
  rw [hcv]
  have hpt : ∀ s : ℝ, ENNReal.ofReal (|c * exp s|) *
      ENNReal.ofReal ((c * exp s)⁻¹ * exp (-(c * exp s) - q / (2 * (c * exp s)))) =
      ENNReal.ofReal (exp (-Real.sqrt (2 * q) * cosh s)) := by
    intro s
    have hp : 0 < c * exp s := by positivity
    rw [abs_of_pos hp, ← ENNReal.ofReal_mul hp.le, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    congr 2
    rw [← h2c, cosh_eq]
    have he : exp (-s) = (exp s)⁻¹ := exp_neg s
    rw [he]
    field_simp
    rw [hc2]
    ring
  simp_rw [hpt]
  rw [lintegral_even _ (fun s => by rw [cosh_neg])]
  rfl

end Verification
