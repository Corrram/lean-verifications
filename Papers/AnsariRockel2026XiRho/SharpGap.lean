import Papers.AnsariRockel2026XiRho.DiagonalBandUnit

/-! # Corollary 1: the sharp global rho-minus-xi maximum

Exact coefficient evaluation and uniqueness over all bivariate copulas.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

private theorem unitBand_sq_profile (v : I) :
    (∫ u : I, unitBandKernel v u ^ 2) =
      if (v : ℝ) ≤ 1 / 2 then Real.sqrt (2 * (v : ℝ)) ^ 3 / 3
      else 1 - 2 * (1 - (v : ℝ)) + Real.sqrt (2 * (1 - (v : ℝ))) ^ 3 / 3 := by
  split_ifs with hv
  · simp_rw [unitBandKernel_lower v _ hv]
    exact integral_ramp_sq _
  · simp_rw [unitBandKernel_upper v _ (by linarith : 1 / 2 ≤ (v : ℝ))]
    rw [integral_complement_reflected_ramp_sq]
    dsimp
    rw [Real.sq_sqrt (by linarith [v.property.2] : 0 ≤ 2 * (1 - (v : ℝ)))]

private theorem unitBand_rho_profile (v : I) :
    (∫ u : I, (1 - (u : ℝ)) * unitBandKernel v u) =
      if (v : ℝ) ≤ 1 / 2 then (v : ℝ) - Real.sqrt (2 * (v : ℝ)) ^ 3 / 6
      else 1 / 2 - Real.sqrt (2 * (1 - (v : ℝ))) ^ 3 / 6 := by
  split_ifs with hv
  · simp_rw [unitBandKernel_lower v _ hv]
    rw [integral_weight_mul_ramp]
    dsimp
    rw [Real.sq_sqrt (by nlinarith [v.property.1] : 0 ≤ 2 * (v : ℝ))]
    ring
  · simp_rw [unitBandKernel_upper v _ (by linarith : 1 / 2 ≤ (v : ℝ))]
    exact integral_weight_complement_reflected_ramp _

/-- Exact xi value of the source's unit-slope diagonal band. -/
theorem unitDiagonalBand_xi : unitDiagonalBand.chatterjeeXi = 3 / 10 := by
  have hs (v : I) : (∫ u : I, unitDiagonalBand.conditionalCDF u v ^ 2) =
      ∫ u : I, unitBandKernel v u ^ 2 :=
    integral_congr_ae ((unitDiagonalBand_conditionalCDF v).fun_comp (fun x : ℝ => x ^ 2))
  unfold Copula.chatterjeeXi
  simp_rw [hs, unitBand_sq_profile]
  rw [integral_unit_two_halves (fun v : ℝ => Real.sqrt (2 * v) ^ 3 / 3)
    (fun v : ℝ => 1 - 2 * v + Real.sqrt (2 * v) ^ 3 / 3) (by fun_prop) (by fun_prop)]
  have he (v : ℝ) : Real.sqrt (2 * v) ^ 3 / 3 + (1 - 2 * v + Real.sqrt (2 * v) ^ 3 / 3) =
      (1 - 2 * v) + (2 / 3) * Real.sqrt (2 * v) ^ 3 := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_add
      ((show Continuous (fun v : ℝ => 1 - 2 * v) by fun_prop).intervalIntegrable _ _)
      ((show Continuous (fun v : ℝ => (2 / 3) * Real.sqrt (2 * v) ^ 3) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_sqrt_two_cube_half,
    intervalIntegral.integral_sub (intervalIntegrable_const)
      ((show Continuous (fun v : ℝ => 2 * v) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  norm_num

/-- Exact rho value, evaluated from the actual conditional distribution. -/
theorem unitDiagonalBand_rho : unitDiagonalBand.spearmanRho = 7 / 10 := by
  have hs (v : I) : (∫ u : I, (1 - (u : ℝ)) * unitDiagonalBand.conditionalCDF u v) =
      ∫ u : I, (1 - (u : ℝ)) * unitBandKernel v u := by
    apply integral_congr_ae
    filter_upwards [unitDiagonalBand_conditionalCDF v] with u hu
    rw [hu]
  rw [rho_conditional_formula]
  simp_rw [hs, unitBand_rho_profile]
  rw [integral_unit_two_halves (fun v : ℝ => v - Real.sqrt (2 * v) ^ 3 / 6)
    (fun v : ℝ => 1 / 2 - Real.sqrt (2 * v) ^ 3 / 6) (by fun_prop) (by fun_prop)]
  have he (v : ℝ) : (v - Real.sqrt (2 * v) ^ 3 / 6) + (1 / 2 - Real.sqrt (2 * v) ^ 3 / 6) =
      (v + 1 / 2) - (1 / 3) * Real.sqrt (2 * v) ^ 3 := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub
      ((show Continuous (fun v : ℝ => v + 1 / 2) by fun_prop).intervalIntegrable _ _)
      ((show Continuous (fun v : ℝ => (1 / 3) * Real.sqrt (2 * v) ^ 3) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_sqrt_two_cube_half,
    intervalIntegral.integral_add (f := fun v : ℝ => v) (g := fun _ => (1 / 2 : ℝ))
      (continuous_id.intervalIntegrable _ _) intervalIntegrable_const,
    integral_id, intervalIntegral.integral_const]
  norm_num

/-- Corollary 1: universal sharp bound, including singular copulas. -/
theorem rho_sub_xi_le (C : Copula 2) : C.spearmanRho - C.chatterjeeXi ≤ 2 / 5 := by
  have h := unitDiagonalBand_support C
  rw [unitDiagonalBand_rho, unitDiagonalBand_xi] at h
  linarith

/-- Corollary 1: equality identifies the unique actual maximizing copula. -/
theorem rho_sub_xi_eq_iff (C : Copula 2) :
    C.spearmanRho - C.chatterjeeXi = 2 / 5 ↔ C = unitDiagonalBand := by
  convert unitDiagonalBand_support_eq_iff C using 1
  rw [unitDiagonalBand_rho, unitDiagonalBand_xi]
  norm_num

/-- The maximum is attained, with the source's exact coefficient pair. -/
theorem sharp_gap_attained : ∃ D : Copula 2,
    D.chatterjeeXi = 3 / 10 ∧ D.spearmanRho = 7 / 10 ∧
    (∀ C : Copula 2, C.spearmanRho - C.chatterjeeXi ≤ D.spearmanRho - D.chatterjeeXi) ∧
    (∀ C : Copula 2, C.spearmanRho - C.chatterjeeXi = D.spearmanRho - D.chatterjeeXi ↔ C = D) :=
  ⟨unitDiagonalBand, unitDiagonalBand_xi, unitDiagonalBand_rho,
    unitDiagonalBand_support, unitDiagonalBand_support_eq_iff⟩

end Papers.AnsariRockel2026XiRho
