import Verification.BernsteinConditional
import Verification.BernsteinProducts

open MeasureTheory ProbabilityTheory Polynomial Set
open scoped unitInterval BigOperators

namespace Verification

/-- Explicit Bernstein Gram entry, with natural-number binomial coefficients. -/
noncomputable def bernsteinGram (m n i j : ℕ) : ℝ :=
  ((m.choose i : ℝ)*(n.choose j : ℝ))/
    (((m : ℝ)+(n : ℝ)+1)*(m+n).choose (i+j))

/-- Derivative Gram entry in a uniform finite-difference form, including the last row. -/
noncomputable def bernsteinDerivativeGram (m i r : ℕ) : ℝ :=
  (m : ℝ)^2 * (bernsteinGram (m-1) (m-1) i r -
    bernsteinGram (m-1) (m-1) (i+1) r -
    bernsteinGram (m-1) (m-1) i (r+1) +
    bernsteinGram (m-1) (m-1) (i+1) (r+1))

theorem bernsteinDerivative_succ (m i : ℕ) (u : I) :
    bernsteinDerivative m (i+1) u =
      (m : ℝ)*(_root_.bernstein (m-1) i u - _root_.bernstein (m-1) (i+1) u) := by
  simp only [bernsteinDerivative,bernsteinPolynomial.derivative_succ,eval_mul,eval_natCast,eval_sub]
  rfl

theorem integral_bernsteinDerivative_product (m i r : ℕ) :
    (∫ u : I, bernsteinDerivative m (i+1) u * bernsteinDerivative m (r+1) u) =
      bernsteinDerivativeGram m i r := by
  simp_rw [bernsteinDerivative_succ]
  have he (u : I) :
      ((m : ℝ)*(_root_.bernstein (m-1) i u - _root_.bernstein (m-1) (i+1) u)) *
      ((m : ℝ)*(_root_.bernstein (m-1) r u - _root_.bernstein (m-1) (r+1) u)) =
      (m : ℝ)^2 * ((_root_.bernstein (m-1) i u * _root_.bernstein (m-1) r u -
        _root_.bernstein (m-1) (i+1) u * _root_.bernstein (m-1) r u) -
        (_root_.bernstein (m-1) i u * _root_.bernstein (m-1) (r+1) u -
        _root_.bernstein (m-1) (i+1) u * _root_.bernstein (m-1) (r+1) u)) := by ring
  simp_rw [he]
  rw [integral_const_mul,integral_sub,integral_sub,integral_sub]
  · simp only [integral_bernstein_product_nat,bernsteinDerivativeGram,bernsteinGram]
    ring
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

end Verification
