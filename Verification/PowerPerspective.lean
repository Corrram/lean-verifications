import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fin.VecNotation

open Set

namespace Verification

/-- A grounded concave function remains concave under the power-perspective transform. -/
theorem concave_power_perspective {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Icc 0 1) f)
    (hf0 : f 0 = 0) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ConcaveOn ℝ (Icc 0 1) (fun x => x^r*f (x^(1-r))) := by
  have hF0 : (0:ℝ)^r*f ((0:ℝ)^(1-r)) = 0 := by
    by_cases hr : r = 0
    · simp [hr,hf0]
    · rw [Real.zero_rpow hr,zero_mul]
  have hprod (x : ℝ) (hx : 0 ≤ x) : x^r*x^(1-r)=x := by
    rw [← Real.rpow_add_of_nonneg hx hr0 (sub_nonneg.mpr hr1)]
    simp
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  let z := a*x+b*y
  have hz0 : 0 ≤ z := add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  by_cases hz : z = 0
  · have hax : a*x=0 := by nlinarith [mul_nonneg ha hx.1,mul_nonneg hb hy.1]
    have hby : b*y=0 := by nlinarith [mul_nonneg ha hx.1,mul_nonneg hb hy.1]
    have hA : a*(x^r*f (x^(1-r)))=0 := by
      rcases mul_eq_zero.mp hax with h | h
      · simp [h]
      · rw [h,hF0,mul_zero]
    have hB : b*(y^r*f (y^(1-r)))=0 := by
      rcases mul_eq_zero.mp hby with h | h
      · simp [h]
      · rw [h,hF0,mul_zero]
    change _ ≤ z^r*f (z^(1-r))
    rw [hz,hF0,hA,hB,add_zero]
  have hzp : 0 < z := lt_of_le_of_ne hz0 (Ne.symm hz)
  have hZ : 0 < z^r := Real.rpow_pos_of_pos hzp _
  have hsum : a*x^r+b*y^r ≤ z^r :=
    (Real.concaveOn_rpow hr0 hr1).2 hx.1 hy.1 ha hb hab
  let w : Fin 3 → ℝ := ![a*x^r/z^r,b*y^r/z^r,1-(a*x^r/z^r+b*y^r/z^r)]
  let p : Fin 3 → ℝ := ![x^(1-r),y^(1-r),0]
  have hw : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i _
    fin_cases i
    · exact div_nonneg (mul_nonneg ha (Real.rpow_nonneg hx.1 _)) hZ.le
    · exact div_nonneg (mul_nonneg hb (Real.rpow_nonneg hy.1 _)) hZ.le
    · change 0 ≤ 1-(a*x^r/z^r+b*y^r/z^r)
      rw [← add_div]
      exact sub_nonneg.mpr ((div_le_one hZ).mpr hsum)
  have hw1 : ∑ i : Fin 3, w i = 1 := by simp [w,Fin.sum_univ_three]
  have hp : ∀ i ∈ (Finset.univ : Finset (Fin 3)), p i ∈ Icc (0:ℝ) 1 := by
    intro i _
    fin_cases i
    · exact ⟨Real.rpow_nonneg hx.1 _,Real.rpow_le_one hx.1 hx.2 (sub_nonneg.mpr hr1)⟩
    · exact ⟨Real.rpow_nonneg hy.1 _,Real.rpow_le_one hy.1 hy.2 (sub_nonneg.mpr hr1)⟩
    · exact ⟨le_rfl,zero_le_one⟩
  have harg : ∑ i : Fin 3, w i * p i = z^(1-r) := by
    simp only [Fin.sum_univ_three]
    change a*x^r/z^r*x^(1-r)+b*y^r/z^r*y^(1-r)+_ * 0 = _
    rw [mul_zero,add_zero]
    calc
      (a*x^r/z^r*x^(1-r)+b*y^r/z^r*y^(1-r)) =
          (a*(x^r*x^(1-r))+b*(y^r*y^(1-r)))/z^r := by field_simp
      _ = z/z^r := by rw [hprod x hx.1,hprod y hy.1]
      _ = z^(1-r) := (div_eq_iff hZ.ne').mpr (by rw [mul_comm]; exact (hprod z hz0).symm)
  have hj := hf.le_map_sum hw hw1 hp
  simp only [smul_eq_mul] at hj
  rw [harg] at hj
  simp only [Fin.sum_univ_three] at hj
  change a*x^r/z^r*f (x^(1-r))+b*y^r/z^r*f (y^(1-r))+_ * f 0 ≤ _ at hj
  rw [hf0,mul_zero,add_zero] at hj
  have hm := mul_le_mul_of_nonneg_left hj hZ.le
  convert hm using 1
  field_simp [hZ.ne']

end Verification
