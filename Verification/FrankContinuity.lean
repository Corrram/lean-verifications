import Verification.FrankDensity
import Mathlib.Analysis.Calculus.DSlope

open ProbabilityTheory Filter
open Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def frankExpSlope (x θ : ℝ) : ℝ :=
  dslope (fun t : ℝ => Real.exp (-t*x)) 0 θ

theorem frankExpSlope_zero (x : ℝ) : frankExpSlope x 0 = -x := by
  simp [frankExpSlope]

theorem continuousAt_frankExpSlope (x : ℝ) : ContinuousAt (frankExpSlope x) 0 := by
  apply continuousAt_dslope_same.mpr
  fun_prop

theorem frankExpSlope_ne {θ : ℝ} (hθ : θ ≠ 0) (x : ℝ) :
    frankExpSlope x θ = (Real.exp (-θ*x)-1)/θ := by
  rw [frankExpSlope, dslope_of_ne _ hθ, slope_def_field]
  simp

noncomputable def frankSlopeQuotient (u v θ : ℝ) : ℝ :=
  frankExpSlope u θ*frankExpSlope v θ/frankExpSlope 1 θ

theorem frankSlopeQuotient_zero (u v : ℝ) : frankSlopeQuotient u v 0 = -u*v := by
  simp only [frankSlopeQuotient, frankExpSlope_zero]
  ring

theorem continuousAt_frankSlopeQuotient (u v : ℝ) : ContinuousAt (frankSlopeQuotient u v) 0 := by
  exact ((continuousAt_frankExpSlope u).mul (continuousAt_frankExpSlope v)).div
    (continuousAt_frankExpSlope 1) (by simp [frankExpSlope_zero])

noncomputable def frankRegularCDF (u v θ : ℝ) : ℝ :=
  -dslope Real.log 1 (1+θ*frankSlopeQuotient u v θ)*frankSlopeQuotient u v θ

theorem frankRegularCDF_zero (u v : ℝ) : frankRegularCDF u v 0 = u*v := by
  simp [frankRegularCDF, frankSlopeQuotient_zero, Real.deriv_log]

theorem continuousAt_frankRegularCDF (u v : ℝ) : ContinuousAt (frankRegularCDF u v) 0 := by
  have hq := continuousAt_frankSlopeQuotient u v
  have hi : ContinuousAt (fun θ : ℝ => 1+θ*frankSlopeQuotient u v θ) 0 :=
    continuousAt_const.add (continuousAt_id.mul hq)
  have hl : ContinuousAt (dslope Real.log 1) (1+0*frankSlopeQuotient u v 0) := by
    simp only [zero_mul, add_zero]
    exact continuousAt_dslope_same.mpr (Real.differentiableAt_log (by norm_num))
  exact (hl.comp (x := 0) hi).neg.mul hq

theorem frankRegularCDF_formula {θ : ℝ} (hθ : θ ≠ 0) (u v : ℝ) :
    frankRegularCDF u v θ =
      -Real.log (1+(Real.exp (-θ*u)-1)*(Real.exp (-θ*v)-1)/(Real.exp (-θ)-1))/θ := by
  have he : Real.exp (-θ)-1 ≠ 0 := sub_ne_zero.mpr (by
    intro h
    have hh := Real.exp_injective (h.trans Real.exp_zero.symm)
    exact hθ (neg_eq_zero.mp hh))
  have hq : θ*frankSlopeQuotient u v θ =
      (Real.exp (-θ*u)-1)*(Real.exp (-θ*v)-1)/(Real.exp (-θ)-1) := by
    unfold frankSlopeQuotient
    simp only [frankExpSlope_ne hθ, mul_one]
    field_simp
  have hl := sub_smul_dslope Real.log 1 (1+θ*frankSlopeQuotient u v θ)
  simp only [add_sub_cancel_left, smul_eq_mul, Real.log_one, sub_zero] at hl
  unfold frankRegularCDF
  apply (eq_div_iff hθ).mpr
  rw [← hq, ← hl]
  ring

theorem frankRegularCDF_positive (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    frankRegularCDF u v θ = (frank θ hθ).cdf ![u,v] := by
  rw [frankRegularCDF_formula hθ.ne', ← frankRealCDF_eq hθ]
  have hd : 1-Real.exp (-θ) ≠ 0 := ne_of_gt
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hd' : Real.exp (-θ)-1 ≠ 0 := by intro h; apply hd; linarith
  unfold frankRealCDF
  congr 2
  congr 1
  unfold frankDen
  field_simp
  ring

theorem frankRegularCDF_negative (θ : ℝ) (hθ : θ < 0) (u v : I) :
    frankRegularCDF u v θ = (frankNegative θ hθ).cdf ![u,v] := by
  rw [frankRegularCDF_formula hθ.ne, frankNegative_cdf_source]

end Verification
