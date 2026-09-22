import Verification.BernsteinDerivativeFactor

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Verification

theorem bernsteinDerivative_boundary_moments (k i : ℕ) (hi : i ≤ k) :
    (∫ u : I, bernsteinDerivative (k+2) (i+1) u * bernsteinDerivative (k+2) (k+2) u) =
      ((k : ℝ)+2) * ((k+2).choose (i+1) : ℝ) *
        (((i : ℝ)+1)*betaMoment (k+i+1) (k-i) -
          ((k : ℝ)+2)*betaMoment (k+i+2) (k-i)) := by
  have he (u : I) : bernsteinDerivative (k+2) (i+1) u * bernsteinDerivative (k+2) (k+2) u =
      (((k : ℝ)+2) * ((k+2).choose (i+1) : ℝ)) *
        (((i : ℝ)+1)*((u : ℝ)^(k+i+1)*(1-(u : ℝ))^(k-i)) -
          ((k : ℝ)+2)*((u : ℝ)^(k+i+2)*(1-(u : ℝ))^(k-i))) := by
    rw [bernsteinDerivative_factor k i hi,show k+2=(k+1)+1 by omega,bernsteinDerivative_last]
    simp only [Nat.cast_add,Nat.cast_one,pow_add,pow_one,pow_two]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_sub]
  · simp only [integral_const_mul,integral_beta_monomial]
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

/-- The printed last-column case of Upsilon, away from the last diagonal entry. -/
theorem bernstein_upsilon_boundary (k i : ℕ) (hi : i ≤ k) :
    (∫ u : I, bernsteinDerivative (k+2) (i+1) u * bernsteinDerivative (k+2) (k+2) u) =
      (((k : ℝ)+2)*((k : ℝ)+1)*((i : ℝ)-(k : ℝ)-1)*((k+2).choose (i+1) : ℝ)) /
        ((2*(k : ℝ)+3)*(2*(k : ℝ)+2)*((2*k+1).choose (k+i+1) : ℝ)) := by
  rw [bernsteinDerivative_boundary_moments k i hi,
    show k+i+2=(k+i+1)+1 by omega,betaMoment_succ (k+i+1) (k-i),betaMoment_binomial (k+i+1) (k-i)]
  have hs : k+i+1+(k-i)=2*k+1 := by omega
  rw [hs]
  simp only [Nat.cast_add,Nat.cast_one,Nat.cast_sub hi]
  have hc : ((2*k+1).choose (k+i+1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : k+i+1 ≤ 2*k+1)).ne'
  have h2 : 2*(k : ℝ)+2 ≠ 0 := by positivity
  have h3 : 2*(k : ℝ)+3 ≠ 0 := by positivity
  have hsum : (k : ℝ)+(i : ℝ)+1+((k : ℝ)-(i : ℝ)) = 2*(k : ℝ)+1 := by ring
  rw [hsum]
  field_simp
  ring

/-- The printed last diagonal entry, also valid for degree one. -/
theorem bernstein_upsilon_corner (k : ℕ) :
    (∫ u : I, bernsteinDerivative (k+1) (k+1) u * bernsteinDerivative (k+1) (k+1) u) =
      ((k : ℝ)+1)^2/(2*(k : ℝ)+1) := by
  simp_rw [bernsteinDerivative_last]
  have he (u : I) : (((k : ℝ)+1)*(u : ℝ)^k) * (((k : ℝ)+1)*(u : ℝ)^k) =
      ((k : ℝ)+1)^2 * (u : ℝ)^(2*k) := by rw [pow_mul]; ring
  simp_rw [he]
  rw [integral_const_mul,Copula.integral_unit_pow]
  push_cast
  ring

end Verification
