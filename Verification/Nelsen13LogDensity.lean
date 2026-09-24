import Verification.Nelsen13
import Copula.Dependence.BB1TotalPositivity

open ProbabilityTheory Set
open Copula

namespace Verification

noncomputable def n13Second (p t : ℝ) : ℝ :=
  p*(1+t)^p/(1+t)^2*(p*(1+t)^p-p+1)*n13Psi p t

noncomputable def n13LogSecondCore (p x : ℝ) : ℝ :=
  Real.log p+(p-2)*Real.log x+Real.log (p*x^p+1-p)+1-x^p

noncomputable def n13LogSecondDeriv (p x : ℝ) : ℝ :=
  (p-2)/x+p^2*x^p/(x*(p*x^p+1-p))-p*x^p/x

theorem n13LogSecondCore_deriv {p x : ℝ} (hx : 0 < x) (hB : p*x^p+1-p ≠ 0) :
    HasDerivAt (n13LogSecondCore p) (n13LogSecondDeriv p x) x := by
  have hP := (hasDerivAt_id x).rpow_const (p := p) (Or.inl hx.ne')
  have hB' := (((hP.const_mul p).add_const 1).sub_const p).log hB
  have hh := (((((Real.hasDerivAt_log hx.ne').const_mul (p-2)).const_add (Real.log p)).add hB').add_const 1).sub hP
  convert hh using 1
  · rfl
  · dsimp [n13LogSecondDeriv]
    rw [Real.rpow_sub_one hx.ne']
    field_simp

theorem n13LogSecondCore_deriv2 {p x : ℝ} (hx : 0 < x) (hB : p*x^p+1-p ≠ 0) :
    HasDerivAt (n13LogSecondDeriv p)
      ((2-p-p*(1-p)*(p*x^p/(p*x^p+1-p))-p^2*(p*x^p/(p*x^p+1-p))^2+
        (1-p)*p*x^p)/x^2) x := by
  have hX := hasDerivAt_id x
  have hP := hX.rpow_const (p := p) (Or.inl hx.ne')
  have hB' := ((hP.const_mul p).add_const 1).sub_const p
  have hh := (((hasDerivAt_const x (p-2)).div hX hx.ne').add
    ((hP.const_mul (p^2)).div (hX.mul hB') (mul_ne_zero hx.ne' hB))).sub
      ((hP.const_mul p).div hX hx.ne')
  convert hh using 1
  · rfl
  · dsimp
    rw [Real.rpow_sub_one hx.ne']
    field_simp
    ring

theorem n13LogSecondCore_deriv2_nonneg {p x : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hx : 0 < x) :
    0 ≤ (2-p-p*(1-p)*(p*x^p/(p*x^p+1-p))-p^2*(p*x^p/(p*x^p+1-p))^2+
        (1-p)*p*x^p)/x^2 := by
  have hY : 0 < p*x^p := mul_pos hp (Real.rpow_pos_of_pos hx _)
  have hB : 0 < p*x^p+1-p := by linarith
  have hR0 : 0 ≤ p*x^p/(p*x^p+1-p) := div_nonneg hY.le hB.le
  have hR1 : p*x^p/(p*x^p+1-p) ≤ 1 := (div_le_one hB).mpr (by linarith)
  have hR2 : (p*x^p/(p*x^p+1-p))^2 ≤ 1 := by nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hR1 (mul_nonneg hp.le (sub_nonneg.mpr hp1))
  have h₂ := mul_le_mul_of_nonneg_left hR2 (sq_nonneg p)
  have h₃ := mul_nonneg (sub_nonneg.mpr hp1) hY.le
  apply div_nonneg _ (sq_nonneg x)
  nlinarith

theorem n13_logSecond_eq {p t : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    Real.log (n13Second p t) = n13LogSecondCore p (1+t) := by
  have hx : 0 < 1+t := by linarith
  have hY : 0 < p*(1+t)^p := mul_pos hp (Real.rpow_pos_of_pos hx _)
  have hB : 0 < p*(1+t)^p-p+1 := by linarith
  unfold n13Second n13Psi n13LogSecondCore
  rw [Real.log_mul (mul_ne_zero (div_ne_zero hY.ne' (pow_ne_zero _ hx.ne')) hB.ne') (Real.exp_ne_zero _),
    Real.log_mul (div_ne_zero hY.ne' (pow_ne_zero _ hx.ne')) hB.ne',
    Real.log_div hY.ne' (pow_ne_zero _ hx.ne'), Real.log_mul hp.ne' (Real.rpow_pos_of_pos hx _).ne',
    Real.log_rpow hx, Real.log_pow, Real.log_exp]
  rw [show p*(1+t)^p-p+1 = p*(1+t)^p+1-p by ring]
  ring

theorem n13Second_pos {p t : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ht : 0 ≤ t) :
    0 < n13Second p t := by
  have hx : 0 < 1+t := by linarith
  have hY : 0 < p*(1+t)^p := mul_pos hp (Real.rpow_pos_of_pos hx _)
  have hB : 0 < p*(1+t)^p-p+1 := by linarith
  exact mul_pos (mul_pos (div_pos hY (sq_pos_of_pos hx)) hB) (Real.exp_pos _)

theorem n13_logSecond_convex {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ (Ici 0) (fun t => Real.log (n13Second p t)) := by
  have hB (t : ℝ) (ht : t ∈ Ici 0) : p*(1+t)^p+1-p ≠ 0 := by
    have hx : 0 < 1+t := by linarith [show 0 ≤ t from ht]
    have hY := mul_pos hp (Real.rpow_pos_of_pos hx p)
    exact ne_of_gt (by linarith)
  have hd (t : ℝ) (ht : t ∈ Ici 0) :
      HasDerivAt (fun t => n13LogSecondCore p (1+t)) (n13LogSecondDeriv p (1+t)) t := by
    simpa only [Function.comp_def, mul_one] using (n13LogSecondCore_deriv (by linarith [show 0 ≤ t from ht] : 0 < 1+t)
      (hB t ht)).comp t ((hasDerivAt_id t).const_add 1)
  have hc : ConvexOn ℝ (Ici 0) (fun t => n13LogSecondCore p (1+t)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
    · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hd t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      have hh := (n13LogSecondCore_deriv2 (by linarith : 0 < 1+t) (hB t ht0)).comp t
        ((hasDerivAt_id t).const_add 1)
      simpa only [Function.comp_def, mul_one] using hh.hasDerivWithinAt
    · intro t ht
      exact n13LogSecondCore_deriv2_nonneg hp hp1 (by linarith [show 0 ≤ t from interior_subset ht])
  apply hc.congr
  intro t ht
  exact (n13_logSecond_eq hp hp1 ht).symm

end Verification
