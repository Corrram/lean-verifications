import Copula.Classical
import Copula.Families.FGM
import Copula.Families.Frechet
import Copula.Rank.ConditionalDerivative

/-!
# Definitions for AnsariRockel2024

The measure representation is connected to the classical CDF representation.
The paper's FGM formula is identified explicitly. Fréchet weights are on M,
W, and independence, in that order; the admissible simplex is `a+b ≤ 1`.
Mardia uses the nonnegative W-weight `θ^2*(1-θ)/2`; see the source audit.
-/

open ProbabilityTheory MeasureTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Section 2.1: every classical copula function has exactly one measure representation. -/
theorem classical_representation (F : (Fin 2 → I) → ℝ) (hF : Copula.IsClassical F) :
    ∃! C : Copula 2, C.cdf = F := hF.existsUnique

/-- Table 5: the FGM CDF on the entire square, for the entire signed parameter range. -/
theorem fgm_cdf (θ : ℝ) (hθ : |θ| ≤ 1) (u v : I) :
    (Copula.fgm θ hθ).cdf ![u, v] =
      (u : ℝ) * (v : ℝ) * (1 + θ * (1 - (u : ℝ)) * (1 - (v : ℝ))) := by
  simpa only [Copula.fgmCDF, Matrix.cons_val_zero, Matrix.cons_val_one] using
    Copula.cdf_fgm θ hθ ![u, v]

/-- The source's derivative normalization of xi, without a copula-density assumption. -/
theorem xi_derivative_formula (C : Copula 2) :
    C.chatterjeeXi =
      6 * (∫ v : I, ∫ u : I, deriv (Copula.cdfSection C v) (u : ℝ) ^ 2) - 2 :=
  Copula.chatterjeeXi_eq_integral_deriv C

end Papers.AnsariRockel2024
