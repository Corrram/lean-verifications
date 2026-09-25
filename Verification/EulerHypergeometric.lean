import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Verification.UnitPowerSubstitution

open MeasureTheory

namespace Verification

/-- Euler's integral representation, with the normalization in equation (26).
The paper uses it where `0 < a < c` and `z ≤ 0`. -/
noncomputable def eulerHypergeometric (a b c z : ℝ) : ℝ :=
  Real.Gamma c / (Real.Gamma a * Real.Gamma (c-a)) *
    ∫ t in (0:ℝ)..1, t^(a-1)*(1-t)^(c-a-1)*(1-t*z)^(-b)

theorem eulerHypergeometric_successor {a : ℝ} (ha : 0<a) (b z : ℝ) :
    eulerHypergeometric a b (a+1) z =
      a * ∫ t in (0:ℝ)..1, t^(a-1)*(1-t*z)^(-b) := by
  unfold eulerHypergeometric
  have h1 : a+1-a=1 := by ring
  rw [h1,Real.Gamma_one,Real.Gamma_add_one ha.ne',mul_one,
    mul_div_cancel_right₀ a (Real.Gamma_pos_of_pos ha).ne']
  simp only [sub_self,Real.rpow_zero,mul_one]

end Verification
