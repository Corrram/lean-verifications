import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Set Filter
open scoped Topology

namespace Verification

theorem hasDerivAt_positivePart_rpow {p : ℝ} (hp : 1<p) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (max 0 y)^p) (p*(max 0 x)^(p-1)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have he : (fun y : ℝ => (max 0 y)^p) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      rw [max_eq_left hy.le,Real.zero_rpow (by linarith : p≠0)]
    have hd := (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq he
    simpa [max_eq_left hx.le,Real.zero_rpow (by linarith : p-1≠0)] using hd
  · have hr : HasDerivAt (fun y : ℝ => y^p) 0 0 := by
      simpa [Real.zero_rpow (by linarith : p-1≠0)] using
        (Real.hasDerivAt_rpow_const (x:=0) (p:=p) (Or.inr hp.le))
    have hl : HasDerivWithinAt (fun y : ℝ => (max 0 y)^p) 0 (Iic 0) 0 := by
      apply (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr
      · intro y hy
        rw [max_eq_left hy,Real.zero_rpow (by linarith : p≠0)]
      · simp [Real.zero_rpow (by linarith : p≠0)]
    have hh : HasDerivWithinAt (fun y : ℝ => (max 0 y)^p) 0 (Ici 0) 0 := by
      apply hr.hasDerivWithinAt.congr
      · intro y hy; rw [max_eq_right hy]
      · simp
    have hd := (hl.union hh).hasDerivAt (by rw [Iic_union_Ici]; exact univ_mem)
    simpa [Real.zero_rpow (by linarith : p-1≠0)] using hd
  · have he : (fun y : ℝ => (max 0 y)^p) =ᶠ[𝓝 x] fun y => y^p := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [max_eq_right hy.le]
    simpa [max_eq_right hx.le] using
      (Real.hasDerivAt_rpow_const (p:=p) (Or.inl hx.ne')).congr_of_eventuallyEq he

end Verification
