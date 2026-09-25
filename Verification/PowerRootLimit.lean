import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field

open Real Filter
open scoped Topology

namespace Verification

theorem power_root_gap_limit {u : ℝ} (hu : 0<u) :
    Tendsto (fun c : ℝ => c*(1-u^(c⁻¹))) atTop (nhds (-Real.log u)) := by
  have hd : HasDerivAt (fun t : ℝ => u^t) (Real.log u) 0 := by
    simpa only [id_eq,mul_one,Real.rpow_zero] using (hasDerivAt_id (0:ℝ)).const_rpow hu
  have h := hd.tendsto_slope_zero_right.comp tendsto_inv_atTop_nhdsGT_zero
  simp only [Function.comp_def,zero_add,Real.rpow_zero,inv_inv,smul_eq_mul] at h
  have hn := h.neg
  convert hn using 1
  funext c
  ring

end Verification
