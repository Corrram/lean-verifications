import Verification.BernsteinDerivativeProducts

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

namespace Verification

noncomputable def bernsteinMixedGram (m i r : ℕ) : ℝ :=
  (m : ℝ) * (bernsteinGram (m-1) m i (r+1) - bernsteinGram (m-1) m (i+1) (r+1))

theorem integral_bernsteinDerivative_mul (m i r : ℕ) :
    (∫ u : I, bernsteinDerivative m (i+1) u * _root_.bernstein m (r+1) u) =
      bernsteinMixedGram m i r := by
  simp_rw [bernsteinDerivative_succ,mul_assoc,sub_mul]
  rw [integral_const_mul,integral_sub]
  · simp only [integral_bernstein_product_nat,bernsteinMixedGram,bernsteinGram]
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

end Verification
