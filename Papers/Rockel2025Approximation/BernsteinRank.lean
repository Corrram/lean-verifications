import Papers.Rockel2025Approximation.BernsteinRho
import Verification.BernsteinXi
import Verification.BernsteinTails

/-! # Bernstein rank formulas and tails

The xi matrix entries are evaluated in a uniform binomial finite-difference form.
This also handles the boundary rows and degree one without separate conventions.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

namespace Papers.Rockel2025Approximation

theorem bernstein_basis_integral (n : ℕ) (i : Fin (n+1)) :
    (∫ u : I, _root_.bernstein n i u) = 1/((n : ℝ)+1) :=
  Verification.integral_bernstein n i

theorem bernstein_lambda_entry (n j s : ℕ) :
    (∫ v : I, _root_.bernstein n j v * _root_.bernstein n s v) =
      ((n.choose j : ℝ)*(n.choose s : ℝ))/
        ((2*(n : ℝ)+1)*(2*n).choose (j+s)) := by
  rw [Verification.integral_bernstein_product_nat]
  congr 2 <;> ring

theorem bernstein_upsilon_entry (m i r : ℕ) :
    (∫ u : I, Verification.bernsteinDerivative m (i+1) u *
      Verification.bernsteinDerivative m (r+1) u) =
      Verification.bernsteinDerivativeGram m i r :=
  Verification.integral_bernsteinDerivative_product m i r

theorem bernstein_conditional_cdf (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) (v : I) :
    (fun u : I => (C.bernstein m n hm hn).conditionalCDF u v) =ᵐ[volume]
      fun u : I => ∑ i : Fin m, ∑ j : Fin n,
        C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
          Verification.bernsteinDerivative m (i.val+1) u * _root_.bernstein n (j.val+1) v :=
  Verification.conditionalCDF_bernstein_grid C m n hm hn v

theorem bernstein_xi_finite_sum (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).chatterjeeXi =
      6 * (∑ i : Fin m, ∑ j : Fin n, ∑ r : Fin m, ∑ s : Fin n,
        C.cdf ![_root_.bernstein.z i.succ,_root_.bernstein.z j.succ] *
        C.cdf ![_root_.bernstein.z r.succ,_root_.bernstein.z s.succ] *
        Verification.bernsteinDerivativeGram m i r *
        Verification.bernsteinGram n n (j.val+1) (s.val+1)) - 2 :=
  Verification.bernstein_xi_gram C m n hm hn

theorem bernstein_lower_tail (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).HasLowerTailDependence 0 :=
  Verification.bernstein_lower_tail C m n hm hn

theorem bernstein_upper_tail (C : Copula 2) (m n : ℕ) (hm : 0<m) (hn : 0<n) :
    (C.bernstein m n hm hn).HasUpperTailDependence 0 :=
  Verification.bernstein_upper_tail C m n hm hn

end Papers.Rockel2025Approximation
