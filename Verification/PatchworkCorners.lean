import Verification.UniformBoundaryCoordinates
import Verification.PatchworkSurvival
import Copula.TailDependence.Basic

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

theorem uniform_coord_lower_eq (m : ℕ) (i : Fin (m+1)) (t : I)
    (ht : (t : ℝ) ≤ 1/((m : ℝ)+1)) :
    (IntervalPartition.uniform (m+1) (by omega)).coord i t =
      if i=0 then (IntervalPartition.uniform (m+1) (by omega)).coord 0 t else 0 := by
  by_cases hi : i=0
  · subst i; simp
  · rw [ite_eq_right hi]
    apply Subtype.ext
    change _ = (0 : ℝ)
    rw [uniform_coord_lower m i t ht,ite_eq_right hi]

theorem uniform_coord_upper_eq (m : ℕ) (i : Fin (m+1)) (t : I)
    (ht : (t : ℝ) ≤ 1/((m : ℝ)+1)) :
    (IntervalPartition.uniform (m+1) (by omega)).coord i (unitInterval.symm t) =
      if i=Fin.last m then (IntervalPartition.uniform (m+1) (by omega)).coord (Fin.last m) (unitInterval.symm t) else 1 := by
  by_cases hi : i=Fin.last m
  · subst i; simp
  · rw [ite_eq_right hi]
    apply Subtype.ext
    have h := uniform_coord_upper m i t ht
    rw [ite_eq_right hi] at h
    change _ = (1 : ℝ)
    linarith

variable {m n : ℕ}

theorem uniform_patchwork_lower_corner
    (A : CellMass (IntervalPartition.uniform (m+1) (by omega)) (IntervalPartition.uniform (n+1) (by omega)))
    (C : Fin (m+1) → Fin (n+1) → Copula 2) (t : I)
    (hm : (t : ℝ) ≤ 1/((m : ℝ)+1)) (hn : (t : ℝ) ≤ 1/((n : ℝ)+1)) :
    (A.patchwork C).diagonal t = A.mass 0 0 * (C 0 0).cdf
      ![(IntervalPartition.uniform (m+1) (by omega)).coord 0 t,
        (IntervalPartition.uniform (n+1) (by omega)).coord 0 t] := by
  rw [Copula.diagonal,CellMass.cdf_patchwork]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · intro j _ hj
      rw [uniform_coord_lower_eq n j t hn,ite_eq_right hj]
      simp
    · simp
  · intro i _ hi
    rw [uniform_coord_lower_eq m i t hm,ite_eq_right hi]
    simp
  · simp

theorem survival_two_one_left (C : Copula 2) (v : I) : C.survival ![1,v]=0 := by
  rw [C.survival_two]
  simp

theorem survival_two_one_right (C : Copula 2) (u : I) : C.survival ![u,1]=0 := by
  rw [C.survival_two]
  simp

theorem uniform_patchwork_upper_corner
    (A : CellMass (IntervalPartition.uniform (m+1) (by omega)) (IntervalPartition.uniform (n+1) (by omega)))
    (C : Fin (m+1) → Fin (n+1) → Copula 2) (t : I)
    (hm : (t : ℝ) ≤ 1/((m : ℝ)+1)) (hn : (t : ℝ) ≤ 1/((n : ℝ)+1)) :
    (A.patchwork C).survival ![unitInterval.symm t,unitInterval.symm t] =
      A.mass (Fin.last m) (Fin.last n) * (C (Fin.last m) (Fin.last n)).survival
        ![(IntervalPartition.uniform (m+1) (by omega)).coord (Fin.last m) (unitInterval.symm t),
          (IntervalPartition.uniform (n+1) (by omega)).coord (Fin.last n) (unitInterval.symm t)] := by
  rw [patchwork_survival]
  rw [Finset.sum_eq_single (Fin.last m)]
  · rw [Finset.sum_eq_single (Fin.last n)]
    · intro j _ hj
      rw [uniform_coord_upper_eq n j t hn,ite_eq_right hj,survival_two_one_right,mul_zero]
    · simp
  · intro i _ hi
    rw [uniform_coord_upper_eq m i t hm,ite_eq_right hi]
    simp only [survival_two_one_left,mul_zero,Finset.sum_const_zero]
  · simp

end Verification
