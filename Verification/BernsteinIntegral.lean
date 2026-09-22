import Copula.Bernstein.Basis
import Copula.Rank.Integration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The exact integral of every Bernstein basis function -/

open MeasureTheory ProbabilityTheory Polynomial Set
open Copula.Bernstein
open scoped unitInterval BigOperators

namespace Verification

private def tailStep (n : ℕ) (i : Fin (n+1)) (j : Fin (n+2)) : ℝ :=
  if (i : ℕ)<j then 1 else 0

private theorem tailStep_difference (n : ℕ) (i k : Fin (n+1)) :
    tailStep n i k.succ-tailStep n i k.castSucc = if k=i then 1 else 0 := by
  by_cases h : k=i
  · subst k
    simp [tailStep]
  · have hk : (k : ℕ) ≠ i := fun he => h (Fin.ext he)
    simp only [tailStep,Fin.val_succ,Fin.val_castSucc,ite_eq_right h]
    split_ifs <;> norm_num <;> omega

private theorem tailPolynomial_derivative (n : ℕ) (i : Fin (n+1)) :
    (polynomial (n+1) (tailStep n i)).derivative =
      Polynomial.C ((n : ℝ)+1)*bernsteinPolynomial ℝ n i := by
  rw [derivative_polynomial]
  congr 1
  simp only [polynomial,tailStep_difference]
  simp

/-- Each degree-n Bernstein basis polynomial has integral 1/(n+1). -/
theorem integral_bernstein (n : ℕ) (i : Fin (n+1)) :
    (∫ u : I, _root_.bernstein n i u) = 1/((n : ℝ)+1) := by
  let P := polynomial (n+1) (tailStep n i)
  have h0 : P.eval 0=0 := by
    have h := eval_polynomial (n+1) (tailStep n i) (0 : I)
    rw [blend_zero] at h
    simpa [P,tailStep] using h
  have h1 : P.eval 1=1 := by
    have h := eval_polynomial (n+1) (tailStep n i) (1 : I)
    rw [blend_one] at h
    simpa [P,tailStep,i.isLt] using h
  have hd (x : ℝ) : HasDerivAt (fun x => P.eval x)
      (((n : ℝ)+1)*(bernsteinPolynomial ℝ n i).eval x) x := by
    have h := P.hasDerivAt x
    simpa only [P,tailPolynomial_derivative,Polynomial.eval_mul,Polynomial.eval_C] using h
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun x _ => hd x) ((show Continuous (fun x : ℝ => ((n : ℝ)+1)*(bernsteinPolynomial ℝ n i).eval x) by fun_prop).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul,h1,h0,sub_zero] at hint
  change (∫ u : I, (bernsteinPolynomial ℝ n i).eval (u : ℝ)) = _
  rw [Copula.integral_unitInterval (fun x => (bernsteinPolynomial ℝ n i).eval x)]
  apply (eq_div_iff (by positivity : (n : ℝ)+1 ≠ 0)).mpr
  linarith only [hint]

end Verification
