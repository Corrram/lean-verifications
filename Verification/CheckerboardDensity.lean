import Verification.PartitionPiece
import Copula.Dependence.Density

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

noncomputable def checkerboardDensity (A : CellMass P Q) (x : Fin 2 → I) : ℝ :=
  ∑ i, ∑ j, (A.mass i j / (P.width i*Q.width j))*
    (partitionPiece P i (fun _ => 1) (x 0)*partitionPiece Q j (fun _ => 1) (x 1))

theorem checkerboardDensity_measurable (A : CellMass P Q) : Measurable (checkerboardDensity A) := by
  unfold checkerboardDensity
  have hP (i : Fin m) : Measurable (partitionPiece P i (fun _ => (1 : ℝ))) := partitionPiece_measurable P i measurable_const
  have hQ (j : Fin n) : Measurable (partitionPiece Q j (fun _ => (1 : ℝ))) := partitionPiece_measurable Q j measurable_const
  fun_prop

theorem checkerboardDensity_nonneg (A : CellMass P Q) (x : Fin 2 → I) : 0≤checkerboardDensity A x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg (div_nonneg (A.nonneg i j) (mul_pos (P.width_pos i) (Q.width_pos j)).le)
  unfold partitionPiece
  split_ifs <;> norm_num

theorem checkerboardDensity_term_integrable (A : CellMass P Q) (i : Fin m) (j : Fin n) :
    Integrable (fun x : Fin 2 → I => (A.mass i j/(P.width i*Q.width j))*
      (partitionPiece P i (fun _ => 1) (x 0)*partitionPiece Q j (fun _ => 1) (x 1))) := by
  refine (integrable_const (|A.mass i j/(P.width i*Q.width j)|)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (measurable_const.mul (((partitionPiece_measurable P i measurable_const).comp (measurable_pi_apply 0)).mul
      ((partitionPiece_measurable Q j measurable_const).comp (measurable_pi_apply 1)))).aestronglyMeasurable
  · unfold partitionPiece
    split_ifs <;> simp only [mul_one,mul_zero,Real.norm_eq_abs,abs_zero,le_refl,abs_nonneg]

theorem checkerboardDensity_integrable (A : CellMass P Q) : Integrable (checkerboardDensity A) := by
  exact integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => checkerboardDensity_term_integrable A i j))

theorem checkerboardDensity_integral_Iic (A : CellMass P Q) (u : Fin 2 → I) :
    (∫ x in Iic u, checkerboardDensity A x)=A.checkerboard.cdf u := by
  have he : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  have hterm (i : Fin m) (j : Fin n) :
      (∫ x in Iic u, (A.mass i j/(P.width i*Q.width j))*
        (partitionPiece P i (fun _ => 1) (x 0)*partitionPiece Q j (fun _ => 1) (x 1))) =
      A.mass i j*((P.coord i (u 0) : ℝ)*(Q.coord j (u 1) : ℝ)) := by
    rw [integral_const_mul]
    conv_lhs => rw [he]
    rw [Copula.integral_cube_Iic_mul,integral_partitionPiece_Iic P i measurable_const (integrable_const _),
      integral_partitionPiece_Iic Q j measurable_const (integrable_const _)]
    simp only [integral_const,smul_eq_mul,mul_one,Measure.real,Measure.restrict_apply_univ,unitInterval.volume_Iic,ENNReal.toReal_ofReal (unitInterval.nonneg _)]
    field_simp [(P.width_pos i).ne', (Q.width_pos j).ne']
  unfold checkerboardDensity
  rw [integral_finsetSum _ (fun i _ => (integrable_finsetSum _ (fun j _ => checkerboardDensity_term_integrable A i j)).integrableOn)]
  simp_rw [integral_finsetSum _ (fun j _ => (checkerboardDensity_term_integrable A _ j).integrableOn),hterm]
  conv_rhs => rw [he]
  rw [CellMass.cdf_checkerboard]

theorem checkerboard_toMeasure_density (A : CellMass P Q) :
    A.checkerboard.toMeasure=(volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal (checkerboardDensity A x)) :=
  Copula.toMeasure_eq_withDensity_of_cdf_integral _ (checkerboardDensity_integrable A)
    (checkerboardDensity_nonneg A) (checkerboardDensity_integral_Iic A)

end Verification
