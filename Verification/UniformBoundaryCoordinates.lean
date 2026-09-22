import Verification.PartitionEmbed

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

theorem uniform_coord_lower (m : ℕ) (i : Fin (m+1)) (t : I)
    (ht : (t : ℝ) ≤ 1/((m : ℝ)+1)) :
    ((IntervalPartition.uniform (m+1) (by omega)).coord i t : ℝ) =
      if i=0 then ((m : ℝ)+1)*(t : ℝ) else 0 := by
  let P := IntervalPartition.uniform (m+1) (by omega)
  change (P.coord i t : ℝ) = _
  have hm : 0 < (m : ℝ)+1 := by positivity
  by_cases hi : i=0
  · subst i
    rw [ite_eq_left rfl,P.coe_coord_of_mem]
    · change ((t : ℝ)-(P.point (Fin.castSucc 0) : ℝ))/P.width 0 = _
      rw [show P.width 0=1/((m : ℝ)+1) by simp [P]]
      simp only [P,IntervalPartition.uniform,Fin.val_castSucc,Fin.val_zero,Nat.cast_zero,zero_div,sub_zero]
      field_simp
    · change (P.point (Fin.castSucc 0) : ℝ) ≤ (t : ℝ)
      simpa [P,IntervalPartition.uniform] using t.property.1
    · change (t : ℝ) ≤ (P.point (Fin.succ 0) : ℝ)
      simpa [P,IntervalPartition.uniform] using ht
  · rw [ite_eq_right hi,P.coord_of_le]
    · rfl
    · have hi' : 1 ≤ (i : ℝ) := by
        have hv : 1 ≤ i.val := by have : i.val ≠ 0 := fun h => hi (Fin.ext h); omega
        exact_mod_cast hv
      change (t : ℝ) ≤ (P.point i.castSucc : ℝ)
      simpa [P,IntervalPartition.uniform] using ht.trans ((div_le_div_iff_of_pos_right hm).mpr hi')

theorem uniform_coord_upper (m : ℕ) (i : Fin (m+1)) (t : I)
    (ht : (t : ℝ) ≤ 1/((m : ℝ)+1)) :
    1-((IntervalPartition.uniform (m+1) (by omega)).coord i (unitInterval.symm t) : ℝ) =
      if i=Fin.last m then ((m : ℝ)+1)*(t : ℝ) else 0 := by
  let P := IntervalPartition.uniform (m+1) (by omega)
  change 1-(P.coord i (unitInterval.symm t) : ℝ) = _
  have hm : 0 < (m : ℝ)+1 := by positivity
  have hs : (m : ℝ)/((m : ℝ)+1)+1/((m : ℝ)+1)=1 := by field_simp
  by_cases hi : i=Fin.last m
  · subst i
    rw [ite_eq_left rfl,P.coe_coord_of_mem]
    · rw [show P.width (Fin.last m)=1/((m : ℝ)+1) by simp [P]]
      simp only [P,IntervalPartition.uniform,Fin.val_castSucc,Fin.val_last,unitInterval.coe_symm_eq,
        Nat.cast_add,Nat.cast_one]
      field_simp
      ring
    · change (P.point (Fin.last m).castSucc : ℝ) ≤ (unitInterval.symm t : ℝ)
      simp only [P,IntervalPartition.uniform,Fin.val_castSucc,Fin.val_last,unitInterval.coe_symm_eq,
        Nat.cast_add,Nat.cast_one]
      linarith
    · change (unitInterval.symm t : ℝ) ≤ (P.point (Fin.last m).succ : ℝ)
      simp only [P,IntervalPartition.uniform,Fin.val_succ,Fin.val_last,unitInterval.coe_symm_eq,
        Nat.cast_add,Nat.cast_one,div_self hm.ne']
      linarith [t.property.1]
  · rw [ite_eq_right hi,P.coord_of_ge]
    · norm_num
    · have hi' : (i : ℝ)+1 ≤ (m : ℝ) := by
        have hv : i.val+1 ≤ m := by
          have hne : i.val ≠ m := fun h => hi (Fin.ext h)
          have := i.isLt
          omega
        exact_mod_cast hv
      have hle : ((i : ℝ)+1)/((m : ℝ)+1) ≤ (m : ℝ)/((m : ℝ)+1) :=
        (div_le_div_iff_of_pos_right hm).mpr hi'
      change (P.point i.succ : ℝ) ≤ (unitInterval.symm t : ℝ)
      simp only [P,IntervalPartition.uniform,Fin.val_succ,unitInterval.coe_symm_eq,Nat.cast_add,Nat.cast_one]
      linarith

end Verification
