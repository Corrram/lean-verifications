import Verification.PartitionMoments
import Copula.Order.Survival

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

variable {m n : ℕ} {P : IntervalPartition m} {Q : IntervalPartition n}

theorem patchwork_survival (A : CellMass P Q) (C : Fin m → Fin n → Copula 2) (u v : I) :
    (A.patchwork C).survival ![u,v] =
      ∑ i, ∑ j, A.mass i j * (C i j).survival ![P.coord i u,Q.coord j v] := by
  have h1 : (∑ i, ∑ j, A.mass i j*(P.coord i u : ℝ)) = u := by
    simp_rw [← Finset.sum_mul,A.row_sum]
    exact P.sum_width_mul_coord u
  have h2 : (∑ i, ∑ j, A.mass i j*(Q.coord j v : ℝ)) = v := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,A.col_sum]
    exact Q.sum_width_mul_coord v
  simp only [Copula.survival_two,CellMass.cdf_patchwork,Matrix.cons_val_zero,Matrix.cons_val_one,
    mul_add,mul_sub,mul_one,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [cellMass_total,h1,h2]

theorem survival_independence_two (u v : I) :
    (Copula.independence 2).survival ![u,v] = (1-(u : ℝ))*(1-(v : ℝ)) := by
  simp only [Copula.survival_two,Copula.cdf_independence,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem survival_comonotonic_two (u v : I) :
    (Copula.comonotonic 2).survival ![u,v] = min (1-(u : ℝ)) (1-(v : ℝ)) := by
  simp only [Copula.survival_two,Copula.cdf_comonotonic_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  rcases le_total (u : ℝ) (v : ℝ) with h | h
  · rw [min_eq_left h,min_eq_right (by linarith)]
    ring
  · rw [min_eq_right h,min_eq_left (by linarith)]
    ring

theorem survival_countermonotonic_two (u v : I) :
    Copula.countermonotonic.survival ![u,v] = max ((1-(u : ℝ))+(1-(v : ℝ))-1) 0 := by
  simp only [Copula.survival_two,Copula.cdf_countermonotonic,Matrix.cons_val_zero,Matrix.cons_val_one]
  by_cases h : (u : ℝ)+(v : ℝ) ≤ 1
  · rw [max_eq_left (by linarith : 0 ≥ (u : ℝ)+(v : ℝ)-1),max_eq_left (by linarith)]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ (u : ℝ)+(v : ℝ)-1),max_eq_right (by linarith)]
    ring

end Verification
