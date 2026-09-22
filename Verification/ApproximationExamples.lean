import Verification.CheckerboardTP2
import Verification.RectangularXi
import Copula.Dependence.Basic

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace Verification.ApproximationExamples

noncomputable def lowerMatrix : CellMass (IntervalPartition.uniform 2 (by omega)) (IntervalPartition.uniform 4 (by omega)) where
  mass := !![1/8,1/4,0,1/8; 1/8,0,1/4,1/8]
  nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  row_sum i := by fin_cases i <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]
  col_sum j := by fin_cases j <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]

noncomputable def coarseMatrix : CellMass (IntervalPartition.uniform 2 (by omega)) (IntervalPartition.uniform 2 (by omega)) where
  mass := !![3/8,1/8; 1/8,3/8]
  nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  row_sum i := by fin_cases i <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]
  col_sum j := by fin_cases j <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]

noncomputable def upperMatrix : CellMass (IntervalPartition.uniform 4 (by omega)) (IntervalPartition.uniform 4 (by omega)) where
  mass := !![1/4,0,0,0; 0,1/8,1/8,0; 0,1/8,1/8,0; 0,0,0,1/4]
  nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  row_sum i := by fin_cases i <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]
  col_sum j := by fin_cases j <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]

noncomputable def shuffleMatrix : CellMass (IntervalPartition.uniform 4 (by omega)) (IntervalPartition.uniform 4 (by omega)) where
  mass := !![1/4,0,0,0; 0,0,1/4,0; 0,1/4,0,0; 0,0,0,1/4]
  nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num
  row_sum i := by fin_cases i <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]
  col_sum j := by fin_cases j <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform]

theorem lowerMatrix_xi : lowerMatrix.checkerboard.chatterjeeXi=1/16 := by
  rw [rectangular_checkerboard_xi (by omega) (by omega),checkerboardXi_trace]
  norm_num [lowerMatrix,cellPrefix,Fin.sum_univ_succ]

theorem coarseMatrix_xi : coarseMatrix.checkerboard.chatterjeeXi=1/8 := by
  rw [rectangular_checkerboard_xi (by omega) (by omega),checkerboardXi_trace]
  norm_num [coarseMatrix,cellPrefix,Fin.sum_univ_succ]

theorem upperMatrix_xi : upperMatrix.checkerboard.chatterjeeXi=5/8 := by
  rw [rectangular_checkerboard_xi (by omega) (by omega),checkerboardXi_trace]
  norm_num [upperMatrix,cellPrefix,Fin.sum_univ_succ]

theorem coarseMatrix_checkMin_xi : coarseMatrix.checkMin.chatterjeeXi=7/16 := by
  rw [rectangular_checkMin_xi (by omega) (by omega),coarseMatrix_xi,cellMass_frobenius]
  norm_num [coarseMatrix,Fin.sum_univ_succ]

theorem shuffleMatrix_checkMin_xi : shuffleMatrix.checkMin.chatterjeeXi=1 := by
  rw [rectangular_checkMin_xi (by omega) (by omega),rectangular_checkerboard_xi (by omega) (by omega),
    checkerboardXi_trace,cellMass_frobenius]
  norm_num [shuffleMatrix,cellPrefix,Fin.sum_univ_succ]

theorem upperMatrix_mtp2 : upperMatrix.checkerboard.HasMTP2Density := by
  apply checkerboard_hasMTP2Density
  intro a b c d hab hcd
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> norm_num [upperMatrix] at *

theorem uniform_four_coord_two_point (i : Fin 4) (j : Fin 3) :
    (IntervalPartition.uniform 4 (by omega)).coord i ((IntervalPartition.uniform 2 (by omega)).point j) =
      if i.val < 2*j.val then 1 else 0 := by
  have he : (IntervalPartition.uniform 2 (by omega)).point j =
      (IntervalPartition.uniform 4 (by omega)).point ⟨2*j.val,by omega⟩ := by
    apply Subtype.ext
    change (j.val : ℝ)/2=((2*j.val : ℕ) : ℝ)/4
    push_cast
    ring
  rw [he,IntervalPartition.coord_point]

theorem lowerMatrix_coarsen (i j : Fin 2) :
    (lowerMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).mass i j=coarseMatrix.mass i j := by
  change lowerMatrix.checkerboard.cdf ![_,_]-lowerMatrix.checkerboard.cdf ![_,_]-
    lowerMatrix.checkerboard.cdf ![_,_]+lowerMatrix.checkerboard.cdf ![_,_]=_
  simp only [CellMass.cdf_checkerboard,IntervalPartition.coord_point,uniform_four_coord_two_point]
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerMatrix,coarseMatrix,Fin.sum_univ_succ]

theorem upperMatrix_coarsen (i j : Fin 2) :
    (upperMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).mass i j=coarseMatrix.mass i j := by
  change upperMatrix.checkerboard.cdf ![_,_]-upperMatrix.checkerboard.cdf ![_,_]-
    upperMatrix.checkerboard.cdf ![_,_]+upperMatrix.checkerboard.cdf ![_,_]=_
  simp only [CellMass.cdf_checkerboard,uniform_four_coord_two_point]
  fin_cases i <;> fin_cases j <;>
    norm_num [upperMatrix,coarseMatrix,Fin.sum_univ_succ]

theorem shuffleMatrix_coarsen (i j : Fin 2) :
    (shuffleMatrix.checkMin.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).mass i j=
      (CellMass.product (IntervalPartition.uniform 2 (by omega)) (IntervalPartition.uniform 2 (by omega))).mass i j := by
  change shuffleMatrix.checkMin.cdf ![_,_]-shuffleMatrix.checkMin.cdf ![_,_]-
    shuffleMatrix.checkMin.cdf ![_,_]+shuffleMatrix.checkMin.cdf ![_,_]=_
  simp only [CellMass.cdf_checkMin,uniform_four_coord_two_point]
  fin_cases i <;> fin_cases j <;>
    norm_num [shuffleMatrix,CellMass.product,IntervalPartition.width_uniform,Fin.sum_univ_succ]

theorem cellMass_ext {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}
    {A B : CellMass P Q} (h : ∀ i j, A.mass i j=B.mass i j) : A=B := by
  cases A
  cases B
  congr
  funext i j
  exact h i j


theorem uniform_two_coord_zero (u : I) :
    ((IntervalPartition.uniform 2 (by omega)).coord 0 u : ℝ)=2*min (u : ℝ) (1/2) := by
  have h := (IntervalPartition.uniform 2 (by omega)).width_mul_coord 0 u
  rw [IntervalPartition.width_uniform] at h
  have h0 : ((IntervalPartition.uniform 2 (by omega)).point (Fin.castSucc (0 : Fin 2)) : ℝ)=0 := by norm_num [IntervalPartition.uniform]
  have h1 : ((IntervalPartition.uniform 2 (by omega)).point (Fin.succ (0 : Fin 2)) : ℝ)=1/2 := by norm_num [IntervalPartition.uniform]
  rw [h0,h1,min_eq_right u.property.1] at h
  norm_num only [Nat.cast_ofNat,sub_zero] at h
  linarith

theorem uniform_two_coord_one (u : I) :
    ((IntervalPartition.uniform 2 (by omega)).coord 1 u : ℝ)=2*(u : ℝ)-2*min (u : ℝ) (1/2) := by
  have h := (IntervalPartition.uniform 2 (by omega)).width_mul_coord 1 u
  rw [IntervalPartition.width_uniform] at h
  have h0 : ((IntervalPartition.uniform 2 (by omega)).point (Fin.castSucc (1 : Fin 2)) : ℝ)=1/2 := by norm_num [IntervalPartition.uniform]
  have h1 : ((IntervalPartition.uniform 2 (by omega)).point (Fin.succ (1 : Fin 2)) : ℝ)=1 := by norm_num [IntervalPartition.uniform]
  rw [h0,h1,min_eq_left u.property.2] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem lowerMatrix_cdf (u v : I) :
    lowerMatrix.checkerboard.cdf ![u,v]=
      (u : ℝ)*(((IntervalPartition.uniform 4 (by omega)).coord 0 v : ℝ)/4+
        ((IntervalPartition.uniform 4 (by omega)).coord 2 v : ℝ)/2+
        ((IntervalPartition.uniform 4 (by omega)).coord 3 v : ℝ)/4)+
      min (u : ℝ) (1/2)*(((IntervalPartition.uniform 4 (by omega)).coord 1 v : ℝ)-
        ((IntervalPartition.uniform 4 (by omega)).coord 2 v : ℝ))/2 := by
  rw [CellMass.cdf_checkerboard]
  norm_num [lowerMatrix,Fin.sum_univ_succ]
  rw [uniform_two_coord_zero,uniform_two_coord_one]
  ring

theorem lowerMatrix_si : lowerMatrix.checkerboard.IsSI := by
  intro a b c v hab hbc
  simp only [lowerMatrix_cdf]
  have hq : 0 ≤ ((IntervalPartition.uniform 4 (by omega)).coord 1 v : ℝ)-
      ((IntervalPartition.uniform 4 (by omega)).coord 2 v : ℝ) := by
    by_cases hv : (v : ℝ) ≤ 1/2
    · have hz := (IntervalPartition.uniform 4 (by omega)).coord_of_le 2 v (by change (v : ℝ) ≤ (2 : ℝ)/4; linarith)
      rw [hz]
      exact sub_nonneg.mpr ((IntervalPartition.uniform 4 (by omega)).coord 1 v).property.1
    · have ho := (IntervalPartition.uniform 4 (by omega)).coord_of_ge 1 v (by change (2 : ℝ)/4 ≤ (v : ℝ); linarith)
      rw [ho]
      exact sub_nonneg.mpr ((IntervalPartition.uniform 4 (by omega)).coord 2 v).property.2
  have hm : ((b : ℝ)-(a : ℝ))*min (c : ℝ) (1/2)+((c : ℝ)-(b : ℝ))*min (a : ℝ) (1/2) ≤
      ((c : ℝ)-(a : ℝ))*min (b : ℝ) (1/2) := by
    change (a : ℝ) ≤ b at hab
    change (b : ℝ) ≤ c at hbc
    simp only [min_def]
    split_ifs <;> nlinarith
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hm)]


/-- Example 4.3, including the actual coarse cell masses and strict inequality. -/
theorem lower_counterexample :
    lowerMatrix.checkerboard.IsSI ∧ lowerMatrix.checkerboard.chatterjeeXi=1/16 ∧
    (lowerMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkerboard.chatterjeeXi=1/8 ∧
    lowerMatrix.checkerboard.chatterjeeXi <
      (lowerMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
        (IntervalPartition.uniform 2 (by omega))).checkerboard.chatterjeeXi := by
  rw [cellMass_ext lowerMatrix_coarsen,lowerMatrix_xi,coarseMatrix_xi]
  exact ⟨lowerMatrix_si,by norm_num⟩

/-- Example 4.4, including a genuine MTP2 density and actual coarsening. -/
theorem upper_counterexample :
    upperMatrix.checkerboard.HasMTP2Density ∧ upperMatrix.checkerboard.chatterjeeXi=5/8 ∧
    (upperMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkMin.chatterjeeXi=7/16 ∧
    (upperMatrix.checkerboard.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkMin.chatterjeeXi < upperMatrix.checkerboard.chatterjeeXi := by
  rw [cellMass_ext upperMatrix_coarsen,upperMatrix_xi,coarseMatrix_checkMin_xi]
  exact ⟨upperMatrix_mtp2,by norm_num⟩

/-- The permutation example between Examples 4.3 and 4.4. -/
theorem shuffle_counterexample :
    shuffleMatrix.checkMin.chatterjeeXi=1 ∧
    (shuffleMatrix.checkMin.cellMass (IntervalPartition.uniform 2 (by omega))
      (IntervalPartition.uniform 2 (by omega))).checkMin.chatterjeeXi=1/4 := by
  rw [cellMass_ext shuffleMatrix_coarsen,shuffleMatrix_checkMin_xi]
  constructor
  · rfl
  · rw [rectangular_checkMin_xi (by omega) (by omega),CellMass.checkerboard_product,
      Copula.chatterjeeXi_independence,cellMass_frobenius]
    norm_num [CellMass.product,IntervalPartition.width_uniform,Fin.sum_univ_succ]


end Verification.ApproximationExamples
