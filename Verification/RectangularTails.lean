import Verification.PatchworkCorners

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval BigOperators Topology

namespace Verification

private theorem eventually_rectangular_small (m n : ℕ) :
    ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t ∧ (t : ℝ) ≤ 1/((m : ℝ)+1) ∧
      (t : ℝ) ≤ 1/((n : ℝ)+1) ∧ ((m : ℝ)+1)*(t : ℝ)+((n : ℝ)+1)*(t : ℝ) ≤ 1 := by
  have hd : 0 < (m : ℝ)+(n : ℝ)+2 := by positivity
  let a : I := ⟨1/((m : ℝ)+(n : ℝ)+2), by
    constructor
    · positivity
    · exact (div_le_one hd).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m,Nat.cast_nonneg (α := ℝ) n])⟩
  have ha : (0 : I) < a := by change (0 : ℝ) < 1/((m : ℝ)+(n : ℝ)+2); positivity
  filter_upwards [(self_mem_nhdsWithin : ∀ᶠ t : I in 𝓝[>] (0 : I), 0 < t),
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with t ht hta
  have hta' : (t : ℝ) ≤ 1/((m : ℝ)+(n : ℝ)+2) := le_of_lt hta
  refine ⟨ht,hta'.trans ?_,hta'.trans ?_,?_⟩
  · exact one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  · exact one_div_le_one_div_of_le (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  · have h := (le_div_iff₀ hd).mp hta'
    nlinarith

private theorem tail_linear_zero (k : ℝ) :
    Tendsto (fun t : I => k*(t : ℝ)) (𝓝[>] (0 : I)) (𝓝 (0 : ℝ)) := by
  simpa using tendsto_const_nhds.mul
    ((continuous_subtype_val.tendsto (0 : I)).mono_left nhdsWithin_le_nhds) (a := k)

variable {m n : ℕ}
variable (A : CellMass (IntervalPartition.uniform (m+1) (by omega)) (IntervalPartition.uniform (n+1) (by omega)))

theorem rectangular_checkerboard_lower_tail : A.checkerboard.HasLowerTailDependence 0 := by
  apply (tail_linear_zero (A.mass 0 0*((m : ℝ)+1)*((n : ℝ)+1))).congr'
  filter_upwards [eventually_rectangular_small m n] with t ht
  rw [Copula.lowerTailRatio,CellMass.checkerboard,uniform_patchwork_lower_corner A _ t ht.2.1 ht.2.2.1]
  simp only [Copula.cdf_independence,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
    uniform_coord_lower m 0 t ht.2.1,uniform_coord_lower n 0 t ht.2.2.1,ite_true]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
  field_simp

theorem rectangular_checkMin_lower_tail :
    A.checkMin.HasLowerTailDependence (A.mass 0 0 * min ((m : ℝ)+1) ((n : ℝ)+1)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_rectangular_small m n] with t ht
  rw [Copula.lowerTailRatio,CellMass.checkMin,uniform_patchwork_lower_corner A _ t ht.2.1 ht.2.2.1]
  simp only [Copula.cdf_comonotonic_two,Matrix.cons_val_zero,Matrix.cons_val_one,uniform_coord_lower m 0 t ht.2.1,
    uniform_coord_lower n 0 t ht.2.2.1,ite_true]
  rw [← min_mul_of_nonneg _ _ t.property.1]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
  field_simp

theorem rectangular_checkW_lower_tail : A.checkW.HasLowerTailDependence 0 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_rectangular_small m n] with t ht
  rw [Copula.lowerTailRatio,CellMass.checkW,uniform_patchwork_lower_corner A _ t ht.2.1 ht.2.2.1]
  simp only [Copula.cdf_countermonotonic,Matrix.cons_val_zero,Matrix.cons_val_one,
    uniform_coord_lower m 0 t ht.2.1,uniform_coord_lower n 0 t ht.2.2.1,ite_true]
  rw [max_eq_left (by linarith [ht.2.2.2]),mul_zero,zero_div]

theorem rectangular_checkerboard_upper_tail : A.checkerboard.HasUpperTailDependence 0 := by
  apply (tail_linear_zero (A.mass (Fin.last m) (Fin.last n)*((m : ℝ)+1)*((n : ℝ)+1))).congr'
  filter_upwards [eventually_rectangular_small m n] with t ht
  rw [Copula.upperTailRatio_eq_survival,CellMass.checkerboard,uniform_patchwork_upper_corner A _ t ht.2.1 ht.2.2.1,
    survival_independence_two]
  simp only [uniform_coord_upper m (Fin.last m) t ht.2.1,uniform_coord_upper n (Fin.last n) t ht.2.2.1,ite_true]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
  field_simp

theorem rectangular_checkMin_upper_tail :
    A.checkMin.HasUpperTailDependence (A.mass (Fin.last m) (Fin.last n) * min ((m : ℝ)+1) ((n : ℝ)+1)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_rectangular_small m n] with t ht
  rw [Copula.upperTailRatio_eq_survival,CellMass.checkMin,uniform_patchwork_upper_corner A _ t ht.2.1 ht.2.2.1,
    survival_comonotonic_two]
  simp only [uniform_coord_upper m (Fin.last m) t ht.2.1,uniform_coord_upper n (Fin.last n) t ht.2.2.1,ite_true]
  rw [← min_mul_of_nonneg _ _ t.property.1]
  have hne : (t : ℝ) ≠ 0 := ne_of_gt ht.1
  field_simp

theorem rectangular_checkW_upper_tail : A.checkW.HasUpperTailDependence 0 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_rectangular_small m n] with t ht
  rw [Copula.upperTailRatio_eq_survival,CellMass.checkW,uniform_patchwork_upper_corner A _ t ht.2.1 ht.2.2.1,
    survival_countermonotonic_two]
  simp only [uniform_coord_upper m (Fin.last m) t ht.2.1,uniform_coord_upper n (Fin.last n) t ht.2.2.1,ite_true]
  rw [max_eq_right (by linarith [ht.2.2.2]),mul_zero,zero_div]

end Verification
