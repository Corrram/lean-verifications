import Verification.CopulaRowOrder
import Verification.FinitePrefixMajorization

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

 theorem checkerboardRow_embed_antitone {n : ℕ} (C : Copula 2) (hC : C.IsSI)
    (m : ℕ) (hm : 0<m) (Q : IntervalPartition n) (j : Fin n) (v : I) :
    Antitone (fun i => checkerboardRow (C.cellMass (IntervalPartition.uniform m hm) Q) i (partitionEmbed Q j v)) := by
  intro i r hir
  simp only [checkerboardRow_embed,checkerboardRow_grid]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (uniform_rowMean_antitone C hC m hm (Q.point j.castSucc) hir) (sub_nonneg.mpr v.property.2))
    (mul_le_mul_of_nonneg_left (uniform_rowMean_antitone C hC m hm (Q.point j.succ) hir) v.property.1)

theorem checkerboardRow_embed_prefix {n : ℕ} (C : Copula 2) (m : ℕ) (hm : 0<m)
    (Q : IntervalPartition n) (j : Fin n) (v : I) (k : Fin (m+1)) :
    (∑ i : Fin m, if i.val < k.val then
      checkerboardRow (C.cellMass (IntervalPartition.uniform m hm) Q) i (partitionEmbed Q j v) else 0) =
    (m : ℝ)*((1-(v : ℝ))*C.cdf ![(IntervalPartition.uniform m hm).point k,Q.point j.castSucc]+
      (v : ℝ)*C.cdf ![(IntervalPartition.uniform m hm).point k,Q.point j.succ]) := by
  simp only [checkerboardRow_embed,checkerboardRow_grid]
  have he (i : Fin m) :
      (if i.val < k.val then (1-(v : ℝ))*copulaRowMean (IntervalPartition.uniform m hm) C i (Q.point j.castSucc)+
        (v : ℝ)*copulaRowMean (IntervalPartition.uniform m hm) C i (Q.point j.succ) else 0) =
      (1-(v : ℝ))*(if i.val < k.val then copulaRowMean (IntervalPartition.uniform m hm) C i (Q.point j.castSucc) else 0)+
        (v : ℝ)*(if i.val < k.val then copulaRowMean (IntervalPartition.uniform m hm) C i (Q.point j.succ) else 0) := by
    split_ifs <;> simp
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,uniform_rowMean_prefix,uniform_rowMean_prefix]
  ring

theorem checkerboardRow_energy_le {n : ℕ} (C : Copula 2) (hC : C.IsCI)
    (m : ℕ) (hm : 0<m) (Q : IntervalPartition n) (j : Fin n) (v : I) :
    (∑ i, (IntervalPartition.uniform m hm).width i *
      checkerboardRow (C.cellMass (IntervalPartition.uniform m hm) Q) i (partitionEmbed Q j v)^2) ≤
      ∫ u : I, C.conditionalCDF u (partitionEmbed Q j v)^2 := by
  let P := IntervalPartition.uniform m hm
  let w := partitionEmbed Q j v
  have hp (k : Fin (m+1)) :
      (∑ i : Fin m, if i.val < k.val then checkerboardRow (C.cellMass P Q) i w else 0) ≤
      ∑ i : Fin m, if i.val < k.val then copulaRowMean P C i w else 0 := by
    rw [checkerboardRow_embed_prefix,uniform_rowMean_prefix]
    exact mul_le_mul_of_nonneg_left (cdf_embed_concavity C hC.2 Q j (P.point k) v) (Nat.cast_nonneg m)
  have ht : (∑ i, copulaRowMean P C i w) = ∑ i, checkerboardRow (C.cellMass P Q) i w := by
    have ha := uniform_rowMean_prefix C m hm (Fin.last m) w
    have hb := checkerboardRow_embed_prefix C m hm Q j v (Fin.last m)
    simp only [Fin.val_last,Fin.is_lt,ite_true] at ha hb
    rw [ha,hb]
    simp only [IntervalPartition.one,Copula.cdf_two_one_left]
    change (m : ℝ)*((Q.point j.castSucc : ℝ)+Q.width j*(v : ℝ)) = _
    unfold IntervalPartition.width
    ring
  have he := majorization_fin_sum_sq (fun i => copulaRowMean P C i w)
    (fun i => checkerboardRow (C.cellMass P Q) i w)
    (checkerboardRow_embed_antitone C hC.1 m hm Q j v) hp ht
  calc
    _ ≤ ∑ i, P.width i * copulaRowMean P C i w^2 := by
      simp only [P,IntervalPartition.width_uniform,← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ _ := copulaRowMean_energy_le P C w

end Verification
