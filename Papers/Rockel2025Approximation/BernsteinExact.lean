import Papers.Rockel2025Approximation.BernsteinRank
import Papers.Rockel2025Approximation.BernsteinKendall
import Verification.BernsteinXiTrace

/-! # Complete Proposition 3.1 for all positive rectangular Bernstein degrees -/

open MeasureTheory ProbabilityTheory Matrix
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

/-- All four printed Upsilon cases, including degree one and the last row/column. -/
theorem bernstein_upsilon_matrix (m : ℕ) (i r : Fin (m+1)) :
    (∫ u : I, Verification.bernsteinDerivative (m+1) (i.val+1) u *
      Verification.bernsteinDerivative (m+1) (r.val+1) u) =
      Verification.bernsteinUpsilonMatrix m i r :=
  Verification.bernsteinUpsilonMatrix_integral m i r

theorem bernstein_lambda_matrix (n : ℕ) (j s : Fin (n+1)) :
    (∫ v : I, _root_.bernstein (n+1) (j.val+1) v * _root_.bernstein (n+1) (s.val+1) v) =
      Verification.bernsteinLambdaMatrix n j s :=
  Verification.bernsteinLambdaMatrix_integral n j s

/-- The exact printed xi trace expression, using the piecewise Upsilon matrix. -/
theorem bernstein_xi_trace (C : Copula 2) (m n : ℕ) :
    (C.bernstein (m+1) (n+1) (by omega) (by omega)).chatterjeeXi =
      6 * Matrix.trace (Verification.bernsteinUpsilonMatrix m * Verification.bernsteinGridMatrix C m n *
        Verification.bernsteinLambdaMatrix n * (Verification.bernsteinGridMatrix C m n)ᵀ) - 2 :=
  Verification.bernstein_xi_trace C m n

/-- Proposition 3.1 in full. Natural m,n encode all positive degrees m+1,n+1. -/
theorem bernstein_all_coefficients (C : Copula 2) (m n : ℕ) :
    let B := C.bernstein (m+1) (n+1) (by omega) (by omega)
    let D := Verification.bernsteinGridMatrix C m n
    B.spearmanRho = 12*(∑ i, ∑ j, (1/(((m : ℝ)+2)*((n : ℝ)+2)))*D i j)-3 ∧
    B.kendallTau = 1-Matrix.trace (Verification.bernsteinThetaMatrix m * D * Verification.bernsteinThetaMatrix n * Dᵀ) ∧
    B.chatterjeeXi = 6*Matrix.trace (Verification.bernsteinUpsilonMatrix m * D * Verification.bernsteinLambdaMatrix n * Dᵀ)-2 ∧
    B.HasLowerTailDependence 0 ∧ B.HasUpperTailDependence 0 := by
  refine ⟨?_,bernstein_tau_trace C m n,bernstein_xi_trace C m n,
    bernstein_lower_tail C (m+1) (n+1) (by omega) (by omega),
    bernstein_upper_tail C (m+1) (n+1) (by omega) (by omega)⟩
  simpa only [Verification.bernsteinGridMatrix,Nat.cast_add,Nat.cast_one,add_assoc,
    show (1 : ℝ)+1=2 by norm_num] using
    bernstein_rho_frobenius C (m+1) (n+1) (by omega) (by omega)

end Papers.Rockel2025Approximation
