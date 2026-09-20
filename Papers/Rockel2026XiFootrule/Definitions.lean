import Copula.Rank.ChatterjeeMixture
import Copula.Rank.Mixture
import Copula.Rank.ConditionalDerivative

/-!
# Definitions for Rockel2026XiFootrule

The direction of xi is coordinate 1 given coordinate 0. Footrule has range
`[-1/2, 1]`. The family in Theorem 2.1 of arXiv:2509.07232v1 is represented
by its probability measure, with its CDF proved below.
-/

open ProbabilityTheory MeasureTheory
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- The Fréchet family `(1-a) Π + a M` in Theorem 2.1. -/
noncomputable def upperBoundary (a : I) : Copula 2 :=
  (Copula.comonotonic 2).mix (Copula.independence 2) a

/-- Correspondence with the source's explicit CDF, including both endpoints. -/
theorem cdf_upperBoundary (a u v : I) :
    (upperBoundary a).cdf ![u, v] =
      (1 - (a : ℝ)) * ((u : ℝ) * (v : ℝ)) + (a : ℝ) * min (u : ℝ) (v : ℝ) := by
  have hinf : (⨅ i : Fin 2, ![u, v] i) = min u v := by
    apply le_antisymm
    · exact le_min (iInf_le _ 0) (iInf_le _ 1)
    · apply le_iInf
      intro i
      fin_cases i
      · exact min_le_left _ _
      · exact min_le_right _ _
  simp only [upperBoundary, Copula.cdf_mix, Copula.cdf_comonotonic, hinf,
    Copula.cdf_independence, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  change (a : ℝ) * min (u : ℝ) (v : ℝ) + (1 - (a : ℝ)) * ((u : ℝ) * (v : ℝ)) = _
  ring

/-- The source's derivative normalization of xi, without a copula-density assumption. -/
theorem xi_derivative_formula (C : Copula 2) :
    C.chatterjeeXi =
      6 * (∫ v : I, ∫ u : I, deriv (Copula.cdfSection C v) (u : ℝ) ^ 2) - 2 :=
  Copula.chatterjeeXi_eq_integral_deriv C

end Papers.Rockel2026XiFootrule
