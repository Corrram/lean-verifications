import Verification.RectangularXi
import Verification.PartitionCellIntegral
import Copula.Dependence.Basic

open MeasureTheory ProbabilityTheory Set Matrix
open Copula
open scoped unitInterval BigOperators

namespace Verification.LTDExample

noncomputable def thirdMatrix (p : ℝ) (hp : p ∈ Icc 0 1) :
    CellMass (IntervalPartition.uniform 3 (by omega)) (IntervalPartition.uniform 3 (by omega)) where
  mass := !![1/3,0,0; 0,p/3,(1-p)/3; 0,(1-p)/3,p/3]
  nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num <;> linarith [hp.1,hp.2]
  row_sum i := by fin_cases i <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform] <;> ring
  col_sum j := by fin_cases j <;> norm_num [Fin.sum_univ_succ,IntervalPartition.width_uniform] <;> ring

theorem thirdMatrix_xi (p : ℝ) (hp : p ∈ Icc 0 1) :
    (thirdMatrix p hp).checkerboard.chatterjeeXi=4/9+2/9*(1-2*p)^2 := by
  rw [rectangular_checkerboard_xi (by omega) (by omega),checkerboardXi_trace]
  norm_num [thirdMatrix,cellPrefix,Fin.sum_univ_succ]
  ring

theorem thirdMatrix_diagonal_grid (p : ℝ) (hp : p ∈ Icc 0 1) :
    (thirdMatrix p hp).checkerboard.cdf
      ![(IntervalPartition.uniform 3 (by omega)).point 2,(IntervalPartition.uniform 3 (by omega)).point 2]=(1+p)/3 := by
  rw [CellMass.cdf_checkerboard]
  norm_num [IntervalPartition.coord_point,thirdMatrix,Fin.sum_univ_succ]
  ring

/-- The matrix printed in Remark 2.6(d) fails even positive quadrant dependence. -/
theorem printedMatrix_not_ltd : ¬(thirdMatrix (1/4) (by norm_num)).checkerboard.IsLTD := by
  intro h
  have hh := h.isPQD ((IntervalPartition.uniform 3 (by omega)).point 2)
    ((IntervalPartition.uniform 3 (by omega)).point 2)
  rw [thirdMatrix_diagonal_grid] at hh
  norm_num [IntervalPartition.uniform] at hh

theorem uniform_three_coord (i : Fin 3) (u : I) :
    ((IntervalPartition.uniform 3 (by omega)).coord i u : ℝ)=
      ![3*min (u : ℝ) (1/3),3*(min (u : ℝ) (2/3)-min (u : ℝ) (1/3)),
        3*((u : ℝ)-min (u : ℝ) (2/3))] i := by
  let P := IntervalPartition.uniform 3 (by omega)
  have h := P.width_mul_coord i u
  have he (j : Fin 4) : (P.point j : ℝ)=(j.val : ℝ)/3 := rfl
  have hw : P.width i=1/3 := IntervalPartition.width_uniform _ _ _
  rw [hw,he,he] at h
  fin_cases i <;> norm_num at h ⊢
  · rw [min_eq_right u.property.1] at h
    linarith
  · linarith
  · rw [min_eq_left u.property.2] at h
    linarith

theorem correctedMatrix_cdf (u v : I) :
    (thirdMatrix (1/3) (by norm_num)).checkerboard.cdf ![u,v]=
      (u : ℝ)*(2*((IntervalPartition.uniform 3 (by omega)).coord 1 v : ℝ)+
        ((IntervalPartition.uniform 3 (by omega)).coord 2 v : ℝ))/3+
      min (u : ℝ) (1/3)*(((IntervalPartition.uniform 3 (by omega)).coord 0 v : ℝ)-
        ((IntervalPartition.uniform 3 (by omega)).coord 1 v : ℝ))+
      (2*min (u : ℝ) (1/3)-min (u : ℝ) (2/3))*
        (((IntervalPartition.uniform 3 (by omega)).coord 1 v : ℝ)-((IntervalPartition.uniform 3 (by omega)).coord 2 v : ℝ))/3 := by
  rw [CellMass.cdf_checkerboard]
  norm_num [thirdMatrix,Fin.sum_univ_succ]
  rw [uniform_three_coord 0 u,uniform_three_coord 1 u,uniform_three_coord 2 u]
  norm_num
  ring

theorem coord_index_antitone {n : ℕ} (P : IntervalPartition n) (u : I) (i j : Fin n) (hij : i ≤ j) :
    P.coord j u ≤ P.coord i u := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · rfl
  · by_cases hu : u ≤ P.point j.castSucc
    · rw [P.coord_of_le j u hu]
      exact (P.coord i u).property.1
    · have hi : P.point i.succ ≤ P.point j.castSucc := P.strictMono.monotone (by exact hij)
      rw [P.coord_of_ge i u (hi.trans (le_of_not_ge hu))]
      exact (P.coord j u).property.2

/-- A corrected matrix proving the intended strict LTD counterexample. -/
theorem correctedMatrix_ltd : (thirdMatrix (1/3) (by norm_num)).checkerboard.IsLTD := by
  intro a b v hab
  have ha := a.property.1
  have hb := b.property.1
  change (a : ℝ) ≤ b at hab
  have hmin : (a : ℝ)*min (b : ℝ) (1/3) ≤ (b : ℝ)*min (a : ℝ) (1/3) := by
    simp only [min_def]
    split_ifs <;> nlinarith
  have htent : (a : ℝ)*(2*min (b : ℝ) (1/3)-min (b : ℝ) (2/3)) ≤
      (b : ℝ)*(2*min (a : ℝ) (1/3)-min (a : ℝ) (2/3)) := by
    simp only [min_def]
    split_ifs <;> nlinarith
  have h01 := coord_index_antitone (IntervalPartition.uniform 3 (by omega)) v 0 1 (by decide)
  have h12 := coord_index_antitone (IntervalPartition.uniform 3 (by omega)) v 1 2 (by decide)
  change (((IntervalPartition.uniform 3 (by omega)).coord 1 v : I) : ℝ) ≤
    ((IntervalPartition.uniform 3 (by omega)).coord 0 v : ℝ) at h01
  change (((IntervalPartition.uniform 3 (by omega)).coord 2 v : I) : ℝ) ≤
    ((IntervalPartition.uniform 3 (by omega)).coord 1 v : ℝ) at h12
  rw [correctedMatrix_cdf,correctedMatrix_cdf]
  nlinarith [mul_nonneg (sub_nonneg.mpr h01) (sub_nonneg.mpr hmin),
    mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr htent)]

end Verification.LTDExample
