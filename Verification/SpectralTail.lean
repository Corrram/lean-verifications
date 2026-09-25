import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

open MeasureTheory Set

namespace Verification

noncomputable def spectralTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (x y : ℝ) : ℝ :=
  ∫ ω, max (x*X ω) (y*Y ω) ∂μ

theorem spectralTail_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (hX : Integrable X μ) (hY : Integrable Y μ) (x y : ℝ) :
    Integrable (fun ω => max (x*X ω) (y*Y ω)) μ :=
  (hX.const_mul x).sup (hY.const_mul y)

theorem spectralTail_nonneg {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (hX : ∀ ω,0≤X ω) {x y : ℝ} (hx : 0≤x) :
    0≤spectralTail μ X Y x y := by
  apply integral_nonneg
  intro ω
  exact (mul_nonneg hx (hX ω)).trans (le_max_left _ _)

theorem spectralTail_mono {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (hXi : Integrable X μ) (hYi : Integrable Y μ)
    (hX : ∀ ω,0≤X ω) (hY : ∀ ω,0≤Y ω) {x₁ x₂ y₁ y₂ : ℝ}
    (hx : x₁≤x₂) (hy : y₁≤y₂) :
    spectralTail μ X Y x₁ y₁≤spectralTail μ X Y x₂ y₂ := by
  apply integral_mono (spectralTail_integrable μ X Y hXi hYi _ _)
    (spectralTail_integrable μ X Y hXi hYi _ _)
  intro ω
  exact max_le_max (mul_le_mul_of_nonneg_right hx (hX ω))
    (mul_le_mul_of_nonneg_right hy (hY ω))

theorem max_four_point {a b c d : ℝ} (hab : a≤b) (hcd : c≤d) :
    max a c+max b d≤max a d+max b c := by
  rcases le_total a c with h|h <;> rcases le_total b d with k|k <;>
    rcases le_total a d with m|m <;> rcases le_total b c with n|n <;>
    simp only [max_eq_left, max_eq_right, *] <;> linarith

theorem spectralTail_submodular {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (hXi : Integrable X μ) (hYi : Integrable Y μ)
    (hX : ∀ ω,0≤X ω) (hY : ∀ ω,0≤Y ω) {x₁ x₂ y₁ y₂ : ℝ}
    (hx : x₁≤x₂) (hy : y₁≤y₂) :
    spectralTail μ X Y x₁ y₁+spectralTail μ X Y x₂ y₂≤
      spectralTail μ X Y x₁ y₂+spectralTail μ X Y x₂ y₁ := by
  unfold spectralTail
  rw [← integral_add (spectralTail_integrable μ X Y hXi hYi _ _)
      (spectralTail_integrable μ X Y hXi hYi _ _),
    ← integral_add (spectralTail_integrable μ X Y hXi hYi _ _)
      (spectralTail_integrable μ X Y hXi hYi _ _)]
  apply integral_mono
    ((spectralTail_integrable μ X Y hXi hYi _ _).add (spectralTail_integrable μ X Y hXi hYi _ _))
    ((spectralTail_integrable μ X Y hXi hYi _ _).add (spectralTail_integrable μ X Y hXi hYi _ _))
  intro ω
  exact max_four_point (mul_le_mul_of_nonneg_right hx (hX ω))
    (mul_le_mul_of_nonneg_right hy (hY ω))

theorem spectralTail_zero_right {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (hX : ∀ ω,0≤X ω) (hXm : ∫ ω,X ω ∂μ=1)
    {x : ℝ} (hx : 0≤x) : spectralTail μ X Y x 0=x := by
  unfold spectralTail
  simp only [zero_mul,max_eq_left (mul_nonneg hx (hX _))]
  rw [integral_const_mul,hXm,mul_one]

theorem spectralTail_zero_left {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (hY : ∀ ω,0≤Y ω) (hYm : ∫ ω,Y ω ∂μ=1)
    {y : ℝ} (hy : 0≤y) : spectralTail μ X Y 0 y=y := by
  unfold spectralTail
  simp only [zero_mul,max_eq_right (mul_nonneg hy (hY _))]
  rw [integral_const_mul,hYm,mul_one]

theorem spectralTail_homogeneous {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω→ℝ) (x y c : ℝ) (hc : 0≤c) :
    spectralTail μ X Y (c*x) (c*y)=c*spectralTail μ X Y x y := by
  unfold spectralTail
  simp only [mul_assoc,← mul_max_of_nonneg _ _ hc]
  exact integral_const_mul c _

end Verification
