import Verification.Nelsen17
import Copula.TailDependence.Derivative

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def n17Diagonal (a t : ℝ) : ℝ :=
  (1+((1+t)^a-1)^2/n17A a)^a⁻¹-1

theorem n17Diagonal_deriv {a t : ℝ} (ht : 1+t ≠ 0)
    (hb : 1+((1+t)^a-1)^2/n17A a ≠ 0) :
    HasDerivAt (n17Diagonal a)
      ((2*((1+t)^a-1)*(a*(1+t)^(a-1))/n17A a)*a⁻¹*
        (1+((1+t)^a-1)^2/n17A a)^(a⁻¹-1)) t := by
  have hh := ((((((hasDerivAt_id t).const_add 1).rpow_const (p := a) (Or.inl ht)).sub_const 1).pow 2).div_const (n17A a)).const_add 1
  convert (hh.rpow_const (p := a⁻¹) (Or.inl hb)).sub_const 1 using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]; ring

theorem n17Diagonal_deriv_zero (a : ℝ) : HasDerivAt (n17Diagonal a) 0 0 := by
  have hh := n17Diagonal_deriv (a := a) (t := 0) (by norm_num) (by simp)
  simpa using hh

theorem n17Diagonal_deriv_one {a : ℝ} (ha : a ≠ 0) : HasDerivAt (n17Diagonal a) 2 1 := by
  have hA := n17A_ne ha
  have hbase : 1+((1+(1:ℝ))^a-1)^2/n17A a = (2:ℝ)^a := by
    norm_num only [show (1:ℝ)+1 = 2 by norm_num]
    change 1+(n17A a)^2/n17A a = (2:ℝ)^a
    field_simp
    dsimp [n17A]
    ring
  have hh := n17Diagonal_deriv (a := a) (t := 1) (by norm_num)
    (by rw [hbase]; exact (Real.rpow_pos_of_pos (by norm_num) a).ne')
  convert hh using 1
  rw [hbase]
  norm_num only [show (1:ℝ)+1 = 2 by norm_num]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have he : a*(a⁻¹-1) = 1-a := by field_simp
  rw [he]
  have hp : (2:ℝ)^(a-1)*(2:ℝ)^(1-a) = 1 := by
    rw [← Real.rpow_add (by norm_num), show a-1+(1-a) = 0 by ring, Real.rpow_zero]
  change 2 = 2*n17A a*(a*(2:ℝ)^(a-1))/n17A a*a⁻¹*(2:ℝ)^(1-a)
  field_simp
  nlinarith [hp]

theorem n17Diagonal_eq (θ : ℝ) (hθ : θ ≠ 0) (t : I) :
    n17Diagonal (-θ) t = (nelsen17 θ hθ).diagonal t := by
  rw [Copula.diagonal, nelsen17_cdf_full]
  simp only [n17Diagonal, n17A, inv_neg, pow_two]

theorem nelsen17_tails (θ : ℝ) (hθ : θ ≠ 0) :
    (nelsen17 θ hθ).HasLowerTailDependence 0 ∧
      (nelsen17 θ hθ).HasUpperTailDependence 0 := by
  constructor
  · exact hasLowerTailDependence_of_hasDerivWithinAt (n17Diagonal_eq θ hθ)
      (n17Diagonal_deriv_zero (-θ)).hasDerivWithinAt
  · simpa only [sub_self] using hasUpperTailDependence_of_hasDerivWithinAt
      (n17Diagonal_eq θ hθ) (n17Diagonal_deriv_one (neg_ne_zero.mpr hθ)).hasDerivWithinAt

end Verification
