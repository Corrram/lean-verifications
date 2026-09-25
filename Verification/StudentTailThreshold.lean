import Verification.StudentNonCI
import Mathlib.Analysis.SpecificLimits.Basic

open ProbabilityTheory MeasureTheory Real Set Filter
open scoped Topology

namespace Verification

theorem student_diagonal_score_negative {r ν x : ℝ} (hr : r∈Ioo (-1) 1)
    (hν : 0<ν) (hx : x<0) :
    studentConditionalScore r ν x x=
      -(1-r)/Real.sqrt ((1+ν*(x⁻¹)^2)*(1-r^2)/(ν+1)) := by
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hp : 0<(1+ν*(x⁻¹)^2)*(1-r^2)/(ν+1) := by positivity
  have he : (ν+x^2)*(1-r^2)/(ν+1)=x^2*((1+ν*(x⁻¹)^2)*(1-r^2)/(ν+1)) := by
    field_simp [hx.ne]
    ring
  rw [studentConditionalScore,he,Real.sqrt_mul (sq_nonneg x),Real.sqrt_sq_eq_abs,abs_of_neg hx]
  have hs := (Real.sqrt_pos.mpr hp).ne'
  field_simp [hx.ne]

theorem student_diagonal_score_tendsto {r ν : ℝ} (hr : r∈Ioo (-1) 1) (hν : 0<ν) :
    Tendsto (fun x => studentConditionalScore r ν x x) atBot
      (𝓝 (-(1-r)/Real.sqrt ((1-r^2)/(ν+1)))) := by
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hp : 0<(1-r^2)/(ν+1) := by positivity
  have hi : Tendsto (fun x : ℝ => x⁻¹) atBot (𝓝 0) := tendsto_inv_atBot_zero
  have hq : Tendsto (fun x : ℝ => (1+ν*(x⁻¹)^2)*(1-r^2)/(ν+1)) atBot
      (𝓝 ((1-r^2)/(ν+1))) := by
    simpa using (((tendsto_const_nhds (x := (1:ℝ))).add ((hi.pow 2).const_mul ν)).mul_const (1-r^2)).div_const (ν+1)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have ht := (tendsto_const_nhds (x := -(1-r))).div hs (Real.sqrt_pos.mpr hp).ne'
  apply ht.congr'
  filter_upwards [eventually_lt_atBot (0:ℝ)] with x hx
  exact (student_diagonal_score_negative hr hν hx).symm

end Verification
