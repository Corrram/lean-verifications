import Verification.CheckerboardDensity
import Verification.CheckerboardInterpolationError

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

variable {m n : ℕ}

theorem partition_exists_Ioc (P : IntervalPartition m) (u : I) (hu : 0 < u) :
    ∃ i : Fin m, P.point i.castSucc < u ∧ u ≤ P.point i.succ := by
  obtain ⟨i,hi,hj⟩ := P.exists_cell u
  rcases lt_or_eq_of_le hi with h | h
  · exact ⟨i,h,hj⟩
  · have hip : 0 < i.val := by
      by_contra hn
      have hz : i.castSucc=0 := by apply Fin.ext; change i.val=0; omega
      rw [hz,P.zero] at h
      exact (ne_of_gt hu) h.symm
    let k : Fin m := ⟨i.val-1,by omega⟩
    have he : k.succ=i.castSucc := by ext; dsimp [k]; omega
    refine ⟨k,?_,?_⟩
    · rw [← h,← he]
      exact P.strictMono Fin.castSucc_lt_succ
    · rw [he,h]

theorem partition_Ioc_index_mono (P : IntervalPartition m) {i j : Fin m} {u v : I}
    (hi : P.point i.castSucc < u ∧ u ≤ P.point i.succ)
    (hj : P.point j.castSucc < v ∧ v ≤ P.point j.succ) (huv : u ≤ v) : i ≤ j := by
  by_contra h
  have he : j.succ ≤ i.castSucc := by show j.val+1 ≤ i.val; omega
  exact (not_lt_of_ge (huv.trans (hj.2.trans (P.strictMono.monotone he)))) hi.1

theorem partitionPiece_of_mem (P : IntervalPartition m) (i r : Fin m) (u : I)
    (hu : P.point r.castSucc < u ∧ u ≤ P.point r.succ) :
    partitionPiece P i (fun _ => (1 : ℝ)) u=if i=r then 1 else 0 := by
  by_cases h : i=r
  · subst i
    simp only [partitionPiece,hu,and_self,ite_true]
  · have hn : ¬ (P.point i.castSucc < u ∧ u ≤ P.point i.succ) := by
      intro hi
      exact h (le_antisymm (partition_Ioc_index_mono P hi hu le_rfl) (partition_Ioc_index_mono P hu hi le_rfl))
    simp only [partitionPiece,hn,ite_false,h]

theorem checkerboardDensity_on_cell {P : IntervalPartition m} {Q : IntervalPartition n}
    (A : CellMass P Q) (i : Fin m) (j : Fin n) (u v : I)
    (hu : P.point i.castSucc < u ∧ u ≤ P.point i.succ)
    (hv : Q.point j.castSucc < v ∧ v ≤ Q.point j.succ) :
    checkerboardDensity A ![u,v]=A.mass i j/(P.width i*Q.width j) := by
  simp only [checkerboardDensity,Matrix.cons_val_zero,Matrix.cons_val_one,
    partitionPiece_of_mem P _ i u hu,partitionPiece_of_mem Q _ j v hv]
  simp

theorem checkerboardDensity_zero_left {P : IntervalPartition m} {Q : IntervalPartition n}
    (A : CellMass P Q) (v : I) : checkerboardDensity A ![0,v]=0 := by
  have hn (i : Fin m) : ¬ P.point i.castSucc < (0 : I) := not_lt_of_ge (P.point i.castSucc).property.1
  simp [checkerboardDensity,partitionPiece,hn]

theorem checkerboardDensity_zero_right {P : IntervalPartition m} {Q : IntervalPartition n}
    (A : CellMass P Q) (u : I) : checkerboardDensity A ![u,0]=0 := by
  have hn (j : Fin n) : ¬ Q.point j.castSucc < (0 : I) := not_lt_of_ge (Q.point j.castSucc).property.1
  simp [checkerboardDensity,partitionPiece,hn]

/-- Every TP2 cell-mass matrix yields an MTP2 Lebesgue density, including zero entries. -/
theorem checkerboard_hasMTP2Density {P : IntervalPartition m} {Q : IntervalPartition n}
    (A : CellMass P Q) (hA : IsTP2 A.mass) : A.checkerboard.HasMTP2Density := by
  refine ⟨checkerboardDensity A,checkerboardDensity_measurable A,checkerboardDensity_nonneg A,?_,checkerboard_toMeasure_density A⟩
  apply (Copula.isMTP2_fin_two_iff _).mpr
  intro a b c d hab hcd
  dsimp only
  by_cases ha : a=0
  · subst a
    rw [checkerboardDensity_zero_left,zero_mul]
    exact mul_nonneg (checkerboardDensity_nonneg A _) (checkerboardDensity_nonneg A _)
  by_cases hc : c=0
  · subst c
    rw [checkerboardDensity_zero_right,mul_zero]
    exact mul_nonneg (checkerboardDensity_nonneg A _) (checkerboardDensity_nonneg A _)
  have ha' : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha)
  have hc' : 0 < c := lt_of_le_of_ne c.property.1 (Ne.symm hc)
  obtain ⟨i,hi⟩ := partition_exists_Ioc P a ha'
  obtain ⟨k,hk⟩ := partition_exists_Ioc P b (ha'.trans_le hab)
  obtain ⟨j,hj⟩ := partition_exists_Ioc Q c hc'
  obtain ⟨l,hl⟩ := partition_exists_Ioc Q d (hc'.trans_le hcd)
  rw [checkerboardDensity_on_cell A i l a d hi hl,checkerboardDensity_on_cell A k j b c hk hj,
    checkerboardDensity_on_cell A i j a c hi hj,checkerboardDensity_on_cell A k l b d hk hl]
  have ht := hA i k j l (partition_Ioc_index_mono P hi hk hab) (partition_Ioc_index_mono Q hj hl hcd)
  have hwi := P.width_pos i
  have hwk := P.width_pos k
  have hwj := Q.width_pos j
  have hwl := Q.width_pos l
  have hn : 0 ≤ (P.width i)⁻¹*(P.width k)⁻¹*(Q.width j)⁻¹*(Q.width l)⁻¹ := by
    positivity
  convert mul_le_mul_of_nonneg_right ht hn using 1  <;> simp only [div_eq_mul_inv,mul_inv_rev]  <;> ring

end Verification
