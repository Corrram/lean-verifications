import Verification.BernsteinIntegral
import Copula.Bernstein.Basic
import Copula.TailDependence.Derivative
import Mathlib.Order.Interval.Set.Infinite

open MeasureTheory ProbabilityTheory Polynomial Set
open Copula.Bernstein
open scoped unitInterval BigOperators

namespace Verification

private theorem polynomial_id (n : ℕ) (hn : 0<n) :
    polynomial n (fun i => (_root_.bernstein.z i : ℝ)) = Polynomial.X := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Icc_infinite (show (0 : ℝ)<1 by norm_num)).mono
  intro x hx
  change (polynomial n (fun i => (_root_.bernstein.z i : ℝ))).eval x = Polynomial.X.eval x
  simpa only [Polynomial.eval_X] using
    (show (polynomial n (fun i => (_root_.bernstein.z i : ℝ))).eval ((⟨x,hx⟩ : I) : ℝ) = x by
      rw [eval_polynomial,blend_id n hn])

private noncomputable def diagonalPolynomial (C : Copula 2) (m n : ℕ) : ℝ[X] :=
  ∑ i : Fin (m+1), ∑ j : Fin (n+1),
    Polynomial.C (C.cdf ![_root_.bernstein.z i,_root_.bernstein.z j]) *
      bernsteinPolynomial ℝ m i * bernsteinPolynomial ℝ n j

private theorem diagonalPolynomial_eval (C : Copula 2) (m n : ℕ)
    (hm : 0<m) (hn : 0<n) (u : I) :
    (diagonalPolynomial C m n).eval (u : ℝ) = (C.bernstein m n hm hn).diagonal u := by
  rw [Copula.diagonal,Copula.cdf_bernstein,Copula.bernsteinCDF_eq_sum]
  simp only [diagonalPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C]
  rfl

private theorem diagonalPolynomial_derivative_zero (C : Copula 2) (m n : ℕ) :
    (diagonalPolynomial C m n).derivative.eval 0 = 0 := by
  simp only [diagonalPolynomial,derivative_sum,derivative_mul,derivative_C,
    zero_mul,zero_add,eval_finsetSum,eval_add,eval_mul,eval_C,
    bernsteinPolynomial.eval_at_0]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hi : i=0 <;> by_cases hj : j=0
  · subst i; subst j; simp
  · subst i; simp
  · subst j; simp
  · have hi0 : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    have hj0 : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [hi0,hj0]

private theorem diagonalPolynomial_derivative_one (C : Copula 2) (m n : ℕ)
    (hm : 0<m) (hn : 0<n) :
    (diagonalPolynomial C m n).derivative.eval 1 = 2 := by
  have hi (i : Fin (m+1)) : ((i : ℕ)=m) ↔ i=Fin.last m := by simp only [Fin.ext_iff,Fin.val_last]
  have hj (j : Fin (n+1)) : ((j : ℕ)=n) ↔ j=Fin.last n := by simp only [Fin.ext_iff,Fin.val_last]
  have hd (k : ℕ) (hk : 0<k) :
      (∑ i : Fin (k+1), (_root_.bernstein.z i : ℝ) *
        (bernsteinPolynomial ℝ k i).derivative.eval 1) = 1 := by
    have h := congrArg (fun p : ℝ[X] => p.derivative.eval 1) (polynomial_id k hk)
    simpa only [polynomial,derivative_sum,derivative_mul,derivative_C,zero_mul,
      zero_add,eval_finsetSum,eval_mul,eval_C,derivative_X,eval_one] using h
  simp only [diagonalPolynomial,derivative_sum,derivative_mul,derivative_C,
    zero_mul,zero_add,eval_finsetSum,eval_add,eval_mul,eval_C,
    bernsteinPolynomial.eval_at_1,hi,hj,Finset.sum_add_distrib]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    _root_.bernstein.z_last (Nat.ne_of_gt hn),Copula.cdf_two_one_right]
  rw [hd m hm]
  rw [Finset.sum_comm]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    _root_.bernstein.z_last (Nat.ne_of_gt hm),Copula.cdf_two_one_left]
  rw [hd n hn]
  norm_num

theorem bernstein_lower_tail (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).HasLowerTailDependence 0 := by
  apply Copula.hasLowerTailDependence_of_hasDerivWithinAt
    (f := fun x => (diagonalPolynomial C m n).eval x) (diagonalPolynomial_eval C m n hm hn)
  have h := (diagonalPolynomial C m n).hasDerivAt 0
  rw [diagonalPolynomial_derivative_zero] at h
  exact h.hasDerivWithinAt

theorem bernstein_upper_tail (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).HasUpperTailDependence 0 := by
  have h := (diagonalPolynomial C m n).hasDerivAt 1
  rw [diagonalPolynomial_derivative_one C m n hm hn] at h
  simpa using Copula.hasUpperTailDependence_of_hasDerivWithinAt
    (f := fun x => (diagonalPolynomial C m n).eval x)
    (diagonalPolynomial_eval C m n hm hn) h.hasDerivWithinAt

end Verification
