import Verification.IntegralHinge

open MeasureTheory Set
open scoped unitInterval

namespace Verification

/-- Affine reciprocal integral on the unit interval. -/
theorem integral_unit_affine_reciprocal (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (∫ v : I, 1 / (a * (v : ℝ) + 1 - a)) =
      -(Real.log (1 - a)) / a := by
  let b : ℝ := 1 - a
  have hb : 0 < b := sub_pos.mpr ha1
  have hsub := intervalIntegral.mul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun x : ℝ => 1 / x) a b
  have hend : a * (1 : ℝ) + b = 1 := by dsimp [b]; ring
  simp only [mul_zero, zero_add, hend] at hsub
  rw [integral_one_div_of_pos hb zero_lt_one] at hsub
  have hlog : Real.log (1 / b) = -Real.log b := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hb.ne']
    simp
  rw [hlog] at hsub
  have he : (fun v : I => 1 / (a * (v : ℝ) + 1 - a)) =
      fun v : I => 1 / (a * (v : ℝ) + b) := by
    funext v
    congr 1
    dsimp [b]
    ring
  rw [he]
  change (∫ v : I, 1 / (a * (v : ℝ) + b)) = -Real.log b / a
  rw [ProbabilityTheory.Copula.integral_unitInterval (fun v : ℝ => 1 / (a * v + b))]
  apply (eq_div_iff ha.ne').mpr
  nlinarith [hsub]

/-- The logarithmic one-variable integral in Nelsen 7's Spearman rho. -/
theorem integral_unit_nelsen7_rational (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    (∫ v : I, (v : ℝ) ^ 2 / (2 * (a * (v : ℝ) + 1 - a))) =
      (3 * a ^ 2 - 2 * a - 2 * (a - 1) ^ 2 * Real.log (1 - a)) /
        (4 * a ^ 3) := by
  have hden (v : I) : 0 < a * (v : ℝ) + 1 - a := by
    have hb : 0 < 1 - a := sub_pos.mpr ha1
    nlinarith [mul_nonneg ha.le v.property.1]
  have hreccont : Continuous (fun v : I => 1 / (a * (v : ℝ) + 1 - a)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro v
    exact (hden v).ne'
  have hrec : Integrable (fun v : I => 1 / (a * (v : ℝ) + 1 - a)) :=
    ProbabilityTheory.Copula.integrable_continuous_unit volume hreccont
  have hlin : Integrable (fun v : I => (v : ℝ) / (2 * a)) :=
    ProbabilityTheory.Copula.integrable_continuous_unit volume (by fun_prop)
  have hconst : Integrable (fun _ : I => (1 - a) / (2 * a ^ 2)) := integrable_const _
  have he (v : I) :
      (v : ℝ) ^ 2 / (2 * (a * (v : ℝ) + 1 - a)) =
        (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2) +
          ((1 - a) ^ 2 / (2 * a ^ 2)) * (1 / (a * (v : ℝ) + 1 - a)) := by
    let d : ℝ := a * (v : ℝ) + 1 - a
    have hd : d ≠ 0 := (hden v).ne'
    change (v : ℝ) ^ 2 / (2 * d) =
      (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2) +
        ((1 - a) ^ 2 / (2 * a ^ 2)) * (1 / d)
    field_simp [ha.ne', hd]
    dsimp [d]
    ring
  simp_rw [he]
  have hsplit :
      (∫ v : I, (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2) +
        ((1 - a) ^ 2 / (2 * a ^ 2)) * (1 / (a * (v : ℝ) + 1 - a))) =
      (∫ v : I, (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2)) +
      (∫ v : I, ((1 - a) ^ 2 / (2 * a ^ 2)) *
        (1 / (a * (v : ℝ) + 1 - a))) := by
    simpa only [Pi.sub_apply] using (integral_add (hlin.sub hconst)
      (hrec.const_mul ((1 - a) ^ 2 / (2 * a ^ 2))))
  rw [hsplit]
  have hpart :
      (∫ v : I, (v : ℝ) / (2 * a) - (1 - a) / (2 * a ^ 2)) =
      (∫ v : I, (v : ℝ) / (2 * a)) -
        (∫ _ : I, (1 - a) / (2 * a ^ 2)) := by
    simpa only [Pi.sub_apply] using (integral_sub hlin hconst)
  rw [hpart]
  have hlast :
      (∫ v : I, ((1 - a) ^ 2 / (2 * a ^ 2)) *
        (1 / (a * (v : ℝ) + 1 - a))) =
      ((1 - a) ^ 2 / (2 * a ^ 2)) *
        (∫ v : I, 1 / (a * (v : ℝ) + 1 - a)) := by
    exact integral_const_mul _ _
  rw [hlast]
  have hlinval : (∫ v : I, (v : ℝ) / (2 * a)) = 1 / (4 * a) := by
    have he' : (fun v : I => (v : ℝ) / (2 * a)) =
        fun v : I => (v : ℝ) * (1 / (2 * a)) := by funext v; ring
    rw [he', integral_mul_const, ProbabilityTheory.Copula.integral_unit_id]
    ring
  rw [hlinval, integral_const,
    integral_unit_affine_reciprocal a ha ha1]
  simp only [probReal_univ, smul_eq_mul, one_mul]
  field_simp [ha.ne']
  ring

end Verification
