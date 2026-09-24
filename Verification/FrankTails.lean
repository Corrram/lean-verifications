import Copula.Families.FrankNegative
import Copula.TailDependence.Derivative

open ProbabilityTheory
open Copula
open scoped unitInterval

namespace Verification

noncomputable def frankDiag (θ t : ℝ) : ℝ :=
  -Real.log (1+(Real.exp (-θ*t)-1)^2/(Real.exp (-θ)-1))/θ

theorem frankDiag_deriv_zero (θ : ℝ) : HasDerivAt (frankDiag θ) 0 0 := by
  have he := ((hasDerivAt_id (0:ℝ)).const_mul (-θ)).exp
  have hb := (((he.sub_const 1).pow 2).div_const (Real.exp (-θ)-1)).const_add 1
  have hl := hb.log (by norm_num : 1+(Real.exp (-θ*0)-1)^2/(Real.exp (-θ)-1) ≠ 0)
  convert hl.neg.div_const θ using 1
  · rfl
  · norm_num

theorem frankDiag_deriv_one {θ : ℝ} (hθ : θ ≠ 0) : HasDerivAt (frankDiag θ) 2 1 := by
  have hd : Real.exp (-θ)-1 ≠ 0 := sub_ne_zero.mpr (by
    intro h
    have := Real.exp_injective (h.trans Real.exp_zero.symm)
    exact hθ (neg_eq_zero.mp this))
  have hbval : 1+(Real.exp (-θ*1)-1)^2/(Real.exp (-θ)-1) = Real.exp (-θ) := by
    simp only [mul_one]
    field_simp
    ring
  have he := ((hasDerivAt_id (1:ℝ)).const_mul (-θ)).exp
  have hb := (((he.sub_const 1).pow 2).div_const (Real.exp (-θ)-1)).const_add 1
  have hn : 1+((fun x : ℝ => Real.exp (-θ*id x)-1)^2) 1 /
      (Real.exp (-θ)-1) ≠ 0 := by
    change 1+(Real.exp (-θ*1)-1)^2/(Real.exp (-θ)-1) ≠ 0
    rw [hbval]
    exact Real.exp_ne_zero _
  have hl := hb.log hn
  convert hl.neg.div_const θ using 1
  · rfl
  · norm_num only [id_eq, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [hbval]
    simp only [mul_one]
    field_simp

theorem frankDiag_positive (θ : ℝ) (hθ : 0 < θ) (t : I) :
    frankDiag θ t = (frank θ hθ).diagonal t := by
  rw [diagonal, frank_cdf_full]
  by_cases ht : t = 0
  · subst t
    simp [frankDiag]
  · simp only [ht, or_self, ite_false]
    unfold frankDiag
    congr 2
    congr 1
    have hd : Real.exp (-θ)-1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hθ)))
    have hd' : 1-Real.exp (-θ) ≠ 0 := by intro h; apply hd; linarith
    field_simp
    ring

theorem frankDiag_negative (θ : ℝ) (hθ : θ < 0) (t : I) :
    frankDiag θ t = (frankNegative θ hθ).diagonal t := by
  rw [diagonal, frankNegative_cdf_source]
  simp [frankDiag, pow_two]

theorem frank_positive_tails (θ : ℝ) (hθ : 0 < θ) :
    (frank θ hθ).HasLowerTailDependence 0 ∧ (frank θ hθ).HasUpperTailDependence 0 := by
  constructor
  · exact hasLowerTailDependence_of_hasDerivWithinAt
      (frankDiag_positive θ hθ) (frankDiag_deriv_zero θ).hasDerivWithinAt
  · simpa using hasUpperTailDependence_of_hasDerivWithinAt
      (frankDiag_positive θ hθ) (frankDiag_deriv_one hθ.ne').hasDerivWithinAt

theorem frank_negative_tails (θ : ℝ) (hθ : θ < 0) :
    (frankNegative θ hθ).HasLowerTailDependence 0 ∧
      (frankNegative θ hθ).HasUpperTailDependence 0 := by
  constructor
  · exact hasLowerTailDependence_of_hasDerivWithinAt
      (frankDiag_negative θ hθ) (frankDiag_deriv_zero θ).hasDerivWithinAt
  · simpa using hasUpperTailDependence_of_hasDerivWithinAt
      (frankDiag_negative θ hθ) (frankDiag_deriv_one hθ.ne).hasDerivWithinAt

end Verification
