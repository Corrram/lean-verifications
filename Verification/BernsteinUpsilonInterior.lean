import Verification.BernsteinDerivativeFactor

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Verification

theorem bernsteinDerivative_product_moments (k i r : ℕ) (hi : i ≤ k) (hr : r ≤ k) :
    (∫ u : I, bernsteinDerivative (k+2) (i+1) u * bernsteinDerivative (k+2) (r+1) u) =
      ((k+2).choose (i+1) : ℝ) * ((k+2).choose (r+1) : ℝ) *
        ((((i : ℝ)+1)*((r : ℝ)+1))*betaMoment (i+r) (k-i+(k-r)) -
          (((k : ℝ)+2)*((i : ℝ)+(r : ℝ)+2))*betaMoment (i+r+1) (k-i+(k-r)) +
          ((k : ℝ)+2)^2*betaMoment (i+r+2) (k-i+(k-r))) := by
  have he (u : I) : bernsteinDerivative (k+2) (i+1) u * bernsteinDerivative (k+2) (r+1) u =
      (((k+2).choose (i+1) : ℝ) * ((k+2).choose (r+1) : ℝ)) *
        ((((i : ℝ)+1)*((r : ℝ)+1))*((u : ℝ)^(i+r)*(1-(u : ℝ))^(k-i+(k-r))) -
          (((k : ℝ)+2)*((i : ℝ)+(r : ℝ)+2))*((u : ℝ)^(i+r+1)*(1-(u : ℝ))^(k-i+(k-r))) +
          ((k : ℝ)+2)^2*((u : ℝ)^(i+r+2)*(1-(u : ℝ))^(k-i+(k-r)))) := by
    rw [bernsteinDerivative_factor k i hi,bernsteinDerivative_factor k r hr]
    simp only [pow_add,pow_one,pow_two]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_add,integral_sub]
  · simp only [integral_const_mul,integral_beta_monomial]
  all_goals exact Copula.integrable_continuous_unit volume (by fun_prop)

/-- The printed interior case of Upsilon, for every degree k+2 and source indices i+1,r+1. -/
theorem bernstein_upsilon_interior (k i r : ℕ) (hi : i ≤ k) (hr : r ≤ k) :
    (∫ u : I, bernsteinDerivative (k+2) (i+1) u * bernsteinDerivative (k+2) (r+1) u) =
      (((k+2).choose (i+1) : ℝ) * ((k+2).choose (r+1) : ℝ)) /
        ((2*(k : ℝ)+1)*((2*k).choose (i+r) : ℝ)) *
        (((i : ℝ)+1)*((r : ℝ)+1) -
          (2*((k : ℝ)+2)*((k : ℝ)+1)*((i+r+2).choose 2 : ℝ))/
            ((2*(k : ℝ)+3)*(2*(k : ℝ)+2))) := by
  rw [bernsteinDerivative_product_moments k i r hi hr,
    betaMoment_succ_succ (i+r) (k-i+(k-r)),betaMoment_succ (i+r) (k-i+(k-r)),
    betaMoment_binomial,Nat.cast_choose_two]
  have hs : i+r+(k-i+(k-r))=2*k := by omega
  rw [hs]
  simp only [Nat.cast_add,Nat.cast_ofNat,Nat.cast_sub hi,Nat.cast_sub hr]
  have hc : ((2*k).choose (i+r) : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega : i+r ≤ 2*k)).ne'
  have h1 : 2*(k : ℝ)+1 ≠ 0 := by positivity
  have h2 : 2*(k : ℝ)+2 ≠ 0 := by positivity
  have h3 : 2*(k : ℝ)+3 ≠ 0 := by positivity
  have hsum : (i : ℝ)+(r : ℝ)+((k : ℝ)-(i : ℝ)+((k : ℝ)-(r : ℝ))) = 2*(k : ℝ) := by ring
  rw [hsum]
  field_simp
  ring

end Verification
