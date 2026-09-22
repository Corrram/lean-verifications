import Verification.PolynomialConditionalCDF
import Copula.Bernstein.Basic

open MeasureTheory ProbabilityTheory Polynomial Set
open scoped unitInterval BigOperators

namespace Verification

/-- First-coordinate Bernstein derivative; the polynomial is evaluated on the closed interval. -/
noncomputable def bernsteinDerivative (m i : ℕ) (u : I) : ℝ :=
  (bernsteinPolynomial ℝ m i).derivative.eval (u : ℝ)

/-- The conditional CDF of every rectangular Bernstein copula is its finite derivative sum. -/
theorem conditionalCDF_bernstein (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) (v : I) :
    (fun u : I => (C.bernstein m n hm hn).conditionalCDF u v) =ᵐ[volume]
      fun u : I => ∑ i : Fin (m+1), ∑ j : Fin (n+1),
        C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j] *
          bernsteinDerivative m i u * _root_.bernstein n j v := by
  let p : ℝ[X] := ∑ i : Fin (m+1), ∑ j : Fin (n+1),
    Polynomial.C (C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j] *
      _root_.bernstein n j v) * bernsteinPolynomial ℝ m i
  have he (u : I) : p.eval (u : ℝ) = (C.bernstein m n hm hn).cdf ![u,v] := by
    rw [Copula.cdf_bernstein,Copula.bernsteinCDF_eq_sum]
    simp only [p,eval_finsetSum,eval_mul,eval_C,Matrix.cons_val_zero,Matrix.cons_val_one]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j] *
      _root_.bernstein n j v * _root_.bernstein m i u =
      C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j] *
      _root_.bernstein m i u * _root_.bernstein n j v
    ring
  have h := conditionalCDF_polynomial (C.bernstein m n hm hn) v p he
  convert h using 1
  funext u
  simp only [p,derivative_sum,derivative_mul,derivative_C,zero_mul,zero_add,
    eval_finsetSum,eval_mul,eval_C,bernsteinDerivative]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end Verification
