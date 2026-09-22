import Verification.IncreasingBandDensity
import Copula.Dependence.Density

/-! # Total positivity after standardizing an increasing fixed-width band -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification.IncreasingBand

variable (B : IncreasingBand)

theorem density_tp2 (hB : Monotone B.lower) :
    IsTP2 (fun u v : I => B.density (u,v)) := by
  intro a b c d hab hcd
  have hw := B.width_pos
  have hl := hB hab
  have hc : (c:ℝ) ≤ d := hcd
  dsimp only [density]
  by_cases had : B.lower a ≤ (d:ℝ) ∧ (d:ℝ) ≤ B.lower a+B.width
  · by_cases hbc : B.lower b ≤ (c:ℝ) ∧ (c:ℝ) ≤ B.lower b+B.width
    · have hac : B.lower a ≤ (c:ℝ) ∧ (c:ℝ) ≤ B.lower a+B.width := ⟨by linarith [hbc.1],by linarith [had.2]⟩
      have hbd : B.lower b ≤ (d:ℝ) ∧ (d:ℝ) ≤ B.lower b+B.width := ⟨by linarith [hbc.1],by linarith [had.2]⟩
      rw [ite_eq_left had,ite_eq_left hbc,ite_eq_left hac,ite_eq_left hbd]
    · rw [ite_eq_left had,ite_eq_right hbc,mul_zero]
      apply mul_nonneg <;> split_ifs <;> positivity
  · rw [ite_eq_right had,zero_mul]
    apply mul_nonneg <;> split_ifs <;> positivity

/-- The density after the probability integral transform remains TP2. -/
theorem standardizedDensity_tp2 (hB : Monotone B.lower) :
    IsTP2 (fun u v : I => B.standardizedDensity (u,v)) := by
  intro a b c d hab hcd
  have h := B.density_tp2 hB a b (unitQuantile B.marginal c) (unitQuantile B.marginal d)
    hab (monotone_unitQuantile B.marginal hcd)
  have hc := B.columnDensity_nonneg (unitQuantile B.marginal c)
  have hd := B.columnDensity_nonneg (unitQuantile B.marginal d)
  dsimp [standardizedDensity,conditionalDensity]
  calc
    _ = (B.density (a,unitQuantile B.marginal d)*B.density (b,unitQuantile B.marginal c)) /
        (B.columnDensity (unitQuantile B.marginal c)*B.columnDensity (unitQuantile B.marginal d)) := by ring
    _ ≤ (B.density (a,unitQuantile B.marginal c)*B.density (b,unitQuantile B.marginal d)) /
        (B.columnDensity (unitQuantile B.marginal c)*B.columnDensity (unitQuantile B.marginal d)) :=
      div_le_div_of_nonneg_right h (mul_nonneg hc hd)
    _ = _ := by ring

/-- This is an MTP2 density of the actual standardized copula measure. -/
theorem copula_hasMTP2Density (hB : Monotone B.lower) : B.copula.HasMTP2Density := by
  refine ⟨fun x => B.standardizedDensity (x 0,x 1),
    B.standardizedDensity_measurable.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)),?_,?_,B.copula_density⟩
  · intro x
    exact div_nonneg (B.density_mem _).1 (B.columnDensity_nonneg _)
  · rw [Copula.isMTP2_fin_two_iff]
    exact B.standardizedDensity_tp2 hB

end Verification.IncreasingBand
