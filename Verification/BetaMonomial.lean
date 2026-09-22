import Verification.BernsteinIntegral
import Mathlib.Data.Nat.Choose.Cast

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Verification

noncomputable def betaMoment (a b : ℕ) : ℝ :=
  (a.factorial : ℝ)*(b.factorial : ℝ)/(a+b+1).factorial

theorem integral_beta_monomial (a b : ℕ) :
    (∫ u : I, (u : ℝ)^a * (1-(u : ℝ))^b) = betaMoment a b := by
  have h := integral_bernstein (a+b) ⟨a,by omega⟩
  simp only [_root_.bernstein_apply,Nat.add_sub_cancel_left,mul_assoc] at h
  rw [integral_const_mul] at h
  have hc : ((a+b).choose a : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : a ≤ a+b)).ne'
  have he : (∫ u : I, (u : ℝ)^a * (1-(u : ℝ))^b) =
      (1/((a+b : ℕ)+1 : ℝ))/((a+b).choose a : ℝ) := by
    apply (eq_div_iff hc).mpr
    simpa only [mul_comm] using h
  rw [he,Nat.cast_add_choose,betaMoment,Nat.factorial_succ]
  have ha : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  have hb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos b).ne'
  have hab : ((a+b).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (a+b)).ne'
  push_cast
  field_simp

theorem betaMoment_binomial (a b : ℕ) :
    betaMoment a b = 1/(((a : ℝ)+(b : ℝ)+1)*((a+b).choose a : ℝ)) := by
  rw [Nat.cast_add_choose,betaMoment,Nat.factorial_succ]
  have ha : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos a).ne'
  have hb : (b.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos b).ne'
  have hab : ((a+b).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (a+b)).ne'
  push_cast
  field_simp

theorem betaMoment_succ (a b : ℕ) :
    betaMoment (a+1) b = ((a : ℝ)+1)/((a : ℝ)+(b : ℝ)+2) * betaMoment a b := by
  simp only [betaMoment,show a+1+b+1=(a+b+1)+1 by omega,Nat.factorial_succ]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem betaMoment_succ_succ (a b : ℕ) :
    betaMoment (a+2) b = (((a : ℝ)+1)*((a : ℝ)+2))/
      (((a : ℝ)+(b : ℝ)+2)*((a : ℝ)+(b : ℝ)+3)) * betaMoment a b := by
  rw [show a+2=(a+1)+1 by omega,betaMoment_succ,betaMoment_succ]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end Verification
