import Verification.BernsteinDerivativeProducts
import Verification.BetaMonomial

open MeasureTheory ProbabilityTheory Polynomial
open scoped unitInterval

namespace Verification

/-- Interior-index Bernstein derivatives factor into a beta monomial and a linear polynomial. -/
theorem bernsteinDerivative_factor (k i : ℕ) (hi : i ≤ k) (u : I) :
    bernsteinDerivative (k+2) (i+1) u =
      ((k+2).choose (i+1) : ℝ) * (u : ℝ)^i * (1-(u : ℝ))^(k-i) *
        (((i : ℝ)+1)-((k : ℝ)+2)*(u : ℝ)) := by
  have ha : ((k : ℝ)+2) * ((k+1).choose i : ℝ) =
      ((i : ℝ)+1) * ((k+2).choose (i+1) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (k+1) i
    rw [mul_comm ((k+1+1).choose (i+1)) (i+1)] at h
    convert congrArg (fun z : ℕ => (z : ℝ)) h using 1 <;> push_cast <;> ring
  have hb : ((k+1).choose (i+1) : ℝ) * ((k : ℝ)+2) =
      ((k+2).choose (i+1) : ℝ) * ((k : ℝ)+1-(i : ℝ)) := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_mul_succ_eq (k+1) (i+1))
    push_cast [Nat.cast_sub (by omega : i+1 ≤ k+1+1)] at h
    push_cast [Nat.cast_sub (by omega : i ≤ k+1)] at h
    convert h using 1
    congr 1
    ring
  rw [bernsteinDerivative_succ]
  simp only [_root_.bernstein_apply,show k+2-1=k+1 by omega,
    show k+1-i=(k-i)+1 by omega,show k+1-(i+1)=k-i by omega,pow_succ,Nat.cast_add,Nat.cast_ofNat]
  linear_combination
    ((u : ℝ)^i * (1-(u : ℝ))^(k-i) * (1-(u : ℝ))) * ha -
    ((u : ℝ)^i * (1-(u : ℝ))^(k-i) * (u : ℝ)) * hb

theorem bernsteinDerivative_last (k : ℕ) (u : I) :
    bernsteinDerivative (k+1) (k+1) u = ((k : ℝ)+1)*(u : ℝ)^k := by
  simp [bernsteinDerivative,bernsteinPolynomial,Polynomial.derivative_pow,Polynomial.eval_pow]

end Verification
