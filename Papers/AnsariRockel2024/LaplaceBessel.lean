import Verification.LaplaceBessel
import Papers.AnsariRockel2024.LaplaceDensity

/-! # Table 1: the Laplace density in its printed Bessel form -/

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Papers.AnsariRockel2024

/-- The radial Laplace integral equals `2K₀(√(2q))` for `q>0`, with `K₀(z)=∫₀^∞e^{-z cosh s}ds`. -/
theorem laplace_radial_eq_besselK0 {q : ℝ} (hq : 0 < q) :
    Verification.laplaceRadialDensity q = 2 * Verification.besselK0 (Real.sqrt (2 * q)) :=
  Verification.laplaceRadialDensity_eq_besselK0 hq

end Papers.AnsariRockel2024
