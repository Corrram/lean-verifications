import Verification.PatchworkRho
import Verification.PartitionMoments

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem checkerboard_rho_centers (A : CellMass P Q) :
    A.checkerboard.spearmanRho =
      12*(∑ i, ∑ j, A.mass i j * (1-partitionCenter P i)*(1-partitionCenter Q j))-3 := by
  rw [CellMass.checkerboard,patchwork_rho_formula]
  simp only [Copula.spearmanRho_independence,mul_zero,zero_div,add_zero]
  have he (i : Fin m) (j : Fin n) :
      A.mass i j * (1-partitionCenter P i)*(1-partitionCenter Q j) =
      A.mass i j - A.mass i j*partitionCenter P i - A.mass i j*partitionCenter Q j +
        A.mass i j*(partitionCenter P i*partitionCenter Q j) := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [cellMass_total,cellMass_first_center,cellMass_second_center]
  dsimp only [partitionCenter]
  ring

theorem uniform_patchwork_rho_correction (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) (C : Copula 2) :
    (A.patchwork (fun _ _ => C)).spearmanRho = A.checkerboard.spearmanRho + C.spearmanRho/((m : ℝ)*(n : ℝ)) := by
  rw [patchwork_rho_correction]
  simp only [IntervalPartition.width_uniform]
  have he (i : Fin m) (j : Fin n) : A.mass i j * (1/(m : ℝ)) * (1/(n : ℝ)) * C.spearmanRho =
      A.mass i j * (C.spearmanRho/((m : ℝ)*(n : ℝ))) := by ring
  simp_rw [he]
  simp_rw [← Finset.sum_mul]
  rw [cellMass_total,one_mul]

/-- The source Omega formula, for arbitrary admissible rectangular cell matrices. -/
theorem rectangular_checkerboard_rho (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkerboard.spearmanRho =
      3*(∑ i : Fin m, ∑ j : Fin n,
        (((2*(m : ℝ)-2*((i : ℝ)+1)+1)*(2*(n : ℝ)-2*((j : ℝ)+1)+1))/((m : ℝ)*(n : ℝ))) * A.mass i j)-3 := by
  rw [checkerboard_rho_centers]
  congr 1
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [partitionCenter]
  rw [IntervalPartition.width_uniform,IntervalPartition.width_uniform]
  simp only [IntervalPartition.uniform,Fin.val_castSucc]
  field_simp
  ring

theorem rectangular_checkMin_rho (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkMin.spearmanRho = A.checkerboard.spearmanRho+1/((m : ℝ)*(n : ℝ)) := by
  simpa only [CellMass.checkMin,Copula.spearmanRho_comonotonic] using
    uniform_patchwork_rho_correction hm hn A (Copula.comonotonic 2)

theorem rectangular_checkW_rho (hm : 0<m) (hn : 0<n)
    (A : CellMass (IntervalPartition.uniform m hm) (IntervalPartition.uniform n hn)) :
    A.checkW.spearmanRho = A.checkerboard.spearmanRho-1/((m : ℝ)*(n : ℝ)) := by
  simpa only [CellMass.checkW,Copula.spearmanRho_countermonotonic,neg_div,sub_eq_add_neg] using
    uniform_patchwork_rho_correction hm hn A Copula.countermonotonic

end Verification
