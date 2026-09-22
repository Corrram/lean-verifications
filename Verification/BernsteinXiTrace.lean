import Verification.BernsteinUpsilon

open MeasureTheory ProbabilityTheory Matrix
open scoped unitInterval BigOperators

namespace Verification

/-- The printed Lambda matrix for degree n+1 and source indices j+1,s+1. -/
noncomputable def bernsteinLambdaMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun j s => bernsteinGram (n+1) (n+1) (j.val+1) (s.val+1)

theorem bernsteinLambdaMatrix_integral (n : ℕ) (j s : Fin (n+1)) :
    (∫ v : I, _root_.bernstein (n+1) (j.val+1) v * _root_.bernstein (n+1) (s.val+1) v) =
      bernsteinLambdaMatrix n j s :=
  integral_bernstein_product_nat _ _ _ _

private theorem lambda_transpose (n : ℕ) : (bernsteinLambdaMatrix n)ᵀ=bernsteinLambdaMatrix n := by
  ext j s
  simp only [Matrix.transpose_apply,← bernsteinLambdaMatrix_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => mul_comm _ _

theorem bernsteinUpsilonMatrix_eq_gram (m : ℕ) (i r : Fin (m+1)) :
    bernsteinUpsilonMatrix m i r = bernsteinDerivativeGram (m+1) i r := by
  rw [← bernsteinUpsilonMatrix_integral,integral_bernsteinDerivative_product]

/-- Proposition 3.1's exact xi trace formula, with the printed piecewise Upsilon matrix. -/
theorem bernstein_xi_trace (C : Copula 2) (m n : ℕ) :
    (C.bernstein (m+1) (n+1) (by omega) (by omega)).chatterjeeXi =
      6 * Matrix.trace (bernsteinUpsilonMatrix m * bernsteinGridMatrix C m n *
        bernsteinLambdaMatrix n * (bernsteinGridMatrix C m n)ᵀ) - 2 := by
  have ht := trace_tensor_contraction (bernsteinUpsilonMatrix m) (bernsteinLambdaMatrix n)
    (bernsteinGridMatrix C m n)
  rw [lambda_transpose] at ht
  rw [bernstein_xi_gram,ht]
  simp only [bernsteinUpsilonMatrix_eq_gram,bernsteinGridMatrix,bernsteinLambdaMatrix,Matrix.of_apply]

end Verification
