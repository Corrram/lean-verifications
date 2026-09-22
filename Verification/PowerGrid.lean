import Verification.EmpiricalRateAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace Verification

/-- Zero-based grid dimension: actual order is floor((n+1)^κ). -/
noncomputable def powerGridIndex (κ : ℝ) (n : ℕ) : ℕ := ⌊((n : ℝ)+1)^κ⌋₊-1

theorem powerGridIndex_succ (κ : ℝ) (hκ : 0≤κ) (n : ℕ) :
    powerGridIndex κ n+1=⌊((n : ℝ)+1)^κ⌋₊ := by
  apply Nat.sub_add_cancel
  apply (Nat.one_le_floor_iff _).mpr
  exact Real.one_le_rpow (by have h := Nat.cast_nonneg (α := ℝ) n; linarith) hκ

theorem powerGridIndex_tendsto (κ : ℝ) (hκ : 0<κ) : Tendsto (powerGridIndex κ) atTop atTop := by
  have hb : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  exact (tendsto_sub_atTop_nat 1).comp (tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hκ).comp hb))

theorem powerGridIndex_bound (κ : ℝ) (hκ : 0≤κ) (hκ' : κ≤1/3) (n : ℕ) :
    (powerGridIndex κ n : ℝ)+1 ≤ ((n : ℝ)+2)^(1/3 : ℝ) := by
  rw [show (powerGridIndex κ n : ℝ)+1=(⌊((n : ℝ)+1)^κ⌋₊ : ℝ) by exact_mod_cast powerGridIndex_succ κ hκ n]
  calc
    _ ≤ ((n : ℝ)+1)^κ := Nat.floor_le (Real.rpow_nonneg (by positivity) κ)
    _ ≤ ((n : ℝ)+1)^(1/3 : ℝ) := Real.rpow_le_rpow_of_exponent_le
      (by have h := Nat.cast_nonneg (α := ℝ) n; linarith) hκ'
    _ ≤ ((n : ℝ)+2)^(1/3 : ℝ) := Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)

theorem powerGridIndex_rate_tendsto (κ : ℝ) (hκ : 0≤κ) (hκ' : κ≤1/3) :
    Tendsto (fun n => ((powerGridIndex κ n : ℝ)+1)*(3*empiricalCDFRadius n+8/((n : ℝ)+1))) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by have h := empiricalCDFRadius_nonneg n; positivity)
    (fun n => mul_le_mul_of_nonneg_right (powerGridIndex_bound κ hκ hκ' n)
      (by have h := empiricalCDFRadius_nonneg n; positivity)) empiricalRankRate_scaled_tendsto

/-- The cubic matrix-arithmetic term is bounded by the sample size. -/
theorem powerGridIndex_cube_le (κ : ℝ) (hκ : 0≤κ) (hκ' : κ≤1/3) (n : ℕ) :
    (powerGridIndex κ n+1)^3 ≤ n+1 := by
  rw [powerGridIndex_succ κ hκ]
  have hb : 1≤(n : ℝ)+1 := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
  have hf := Nat.floor_le (Real.rpow_nonneg (by positivity : 0≤(n : ℝ)+1) κ)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) ⌊((n : ℝ)+1)^κ⌋₊) hf 3
  have he : (((n : ℝ)+1)^κ)^3 ≤ (n : ℝ)+1 := by
    rw [← Real.rpow_mul_natCast (by positivity)]
    exact (Real.rpow_le_rpow_of_exponent_le hb (show κ*(3 : ℕ)≤1 by norm_num; linarith)).trans_eq (Real.rpow_one _)
  exact_mod_cast hpow.trans he

end Verification
