import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Copula.Rank.ConditionalCDF

open ProbabilityTheory MeasureTheory Set
open scoped unitInterval

namespace Verification

theorem integral_unit_rpow_substitution {θ : ℝ} (hθ : 0<θ) (f : ℝ → ℝ) :
    (∫ u : I, f ((u:ℝ)^θ))=
      (1/θ)*(∫ t in (0:ℝ)..1, t^(1/θ-1)*f t) := by
  let a := 1/θ
  have ha : 0<a := one_div_pos.mpr hθ
  let g : ℝ → ℝ := (Iic (1:ℝ)).indicator (fun u => f (u^θ))
  have hh := integral_comp_rpow_Ioi g ha.ne'
  rw [abs_of_pos ha] at hh
  have he : (∫ x in Ioi (0:ℝ), (a*x^(a-1)) • g (x^a))=
      ∫ x in Ioi (0:ℝ), (Iic (1:ℝ)).indicator (fun t => a*(t^(a-1)*f t)) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx' : 0<x := hx
    have hp : (x^a)^θ=x := by
      rw [← Real.rpow_mul hx'.le]
      dsimp [a]
      rw [one_div_mul_cancel hθ.ne',Real.rpow_one]
    by_cases h1 : x≤1
    · have hpow : x^a≤1 := Real.rpow_le_one hx'.le h1 ha.le
      simp only [g,indicator_of_mem (show x^a∈Iic (1:ℝ) from hpow),
        indicator_of_mem (show x∈Iic (1:ℝ) from h1),smul_eq_mul,hp]
      ring
    · have hpow : ¬x^a≤1 := not_le.mpr (Real.one_lt_rpow (lt_of_not_ge h1) ha)
      simp only [g,indicator_of_notMem (show x^a∉Iic (1:ℝ) from hpow),
        indicator_of_notMem (show x∉Iic (1:ℝ) from h1),smul_zero]
  rw [he] at hh
  rw [setIntegral_indicator measurableSet_Iic] at hh
  dsimp only [g] at hh
  rw [setIntegral_indicator measurableSet_Iic] at hh
  have hs : Ioi (0:ℝ) ∩ Iic 1=Ioc 0 1 := by ext x; simp
  rw [hs,integral_const_mul] at hh
  rw [Copula.integral_unitInterval (fun u => f (u^θ)),
    intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
  exact hh.symm

end Verification
