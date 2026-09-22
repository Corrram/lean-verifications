import Verification.RankOverlapMatrix

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

/-- A fine rank cell can overlap only these two explicitly computable coarse bins. -/
theorem uniform_overlap_candidates (K n : ℕ) (hK : 0<K) (hn : 0<n) (hKn : K≤n)
    (i : Fin K) (r : Fin n)
    (h : 0<cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) i r) :
    i.val=r.val*K/n ∨ i.val=r.val*K/n+1 := by
  let P := IntervalPartition.uniform K hK
  let Q := IntervalPartition.uniform n hn
  have hv : max (P.point i.castSucc : ℝ) (Q.point r.castSucc) <
      min (P.point i.succ : ℝ) (Q.point r.succ) := by
    change 0<(volume : Measure I).real (Ico (P.point i.castSucc) (P.point i.succ) ∩ Ico (Q.point r.castSucc) (Q.point r.succ)) at h
    rw [Measure.real,Ico_inter_Ico,unitInterval.volume_Ico,ENNReal.toReal_ofReal'] at h
    change 0<max (min (P.point i.succ : ℝ) (Q.point r.succ)-max (P.point i.castSucc : ℝ) (Q.point r.castSucc)) 0 at h
    exact sub_pos.mp ((lt_max_iff.mp h).resolve_right (lt_irrefl 0))
  have h1 : (P.point i.castSucc : ℝ)<Q.point r.succ :=
    (le_max_left _ _).trans_lt (hv.trans_le (min_le_right _ _))
  have h2 : (Q.point r.castSucc : ℝ)<P.point i.succ :=
    (le_max_right _ _).trans_lt (hv.trans_le (min_le_left _ _))
  change (i.val : ℝ)/(K : ℝ)<((r.val+1 : ℕ) : ℝ)/(n : ℝ) at h1
  change (r.val : ℝ)/(n : ℝ)<((i.val+1 : ℕ) : ℝ)/(K : ℝ) at h2
  have h1' : i.val*n < (r.val+1)*K := by
    exact_mod_cast (div_lt_div_iff₀ (Nat.cast_pos.mpr hK) (Nat.cast_pos.mpr hn)).mp h1
  have h2' : r.val*K < (i.val+1)*n := by
    exact_mod_cast (div_lt_div_iff₀ (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hK)).mp h2
  have ha : r.val*K/n ≤ i.val := by
    have hh := (Nat.div_lt_iff_lt_mul hn).mpr h2'
    omega
  have hb : i.val ≤ r.val*K/n+1 := by
    have hrem := Nat.mod_lt (r.val*K) hn
    have he := Nat.mod_add_div (r.val*K) n
    by_contra hh
    have hi : r.val*K/n+2 ≤ i.val := by omega
    have him := Nat.mul_le_mul_right n hi
    nlinarith
  omega

theorem uniform_overlap_two_slots (K n : ℕ) (hK : 0<K) (hn : 0<n) (hKn : K≤n)
    (i : Fin K) (r : Fin n) :
    (∑ b : Fin 2, if i.val=r.val*K/n+b.val then
      cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) i r else 0) =
      cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) i r := by
  let z := cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) i r
  have hz : 0≤z := measureReal_nonneg
  simp only [Fin.sum_univ_two,Fin.val_zero,Fin.val_one,Nat.add_zero]
  by_cases h0 : i.val=r.val*K/n
  · simp [h0]
  by_cases h1 : i.val=r.val*K/n+1
  · simp [h1]
  have he : z=0 := by
    apply le_antisymm _ hz
    by_contra hh
    have hp := uniform_overlap_candidates K n hK hn hKn i r (lt_of_not_ge hh)
    exact hp.elim h0 h1
  simp only [h0,h1,ite_false,zero_add]
  exact he.symm

/-- Four candidate slots per observation reconstruct the exact source matrix.
The two candidate indices in each coordinate are obtained by integer division. -/
theorem rankCopula_cellMass_four_slots (K n : ℕ) (hK : 0<K) (hn : 0<n) (hKn : K≤n)
    (rx ry : Equiv.Perm (Fin n)) (i j : Fin K) :
    ((rankCopula n hn rx ry).cellMass (IntervalPartition.uniform K hK) (IntervalPartition.uniform K hK)).mass i j =
    (n : ℝ)*∑ k : Fin n, ∑ a : Fin 2, ∑ b : Fin 2,
      (if i.val=(rx k).val*K/n+a.val then cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) i (rx k) else 0)*
      (if j.val=(ry k).val*K/n+b.val then cellOverlap (IntervalPartition.uniform K hK) (IntervalPartition.uniform n hn) j (ry k) else 0) := by
  rw [rankCopula_cellMass hn]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul_sum,uniform_overlap_two_slots K n hK hn hKn i (rx k),uniform_overlap_two_slots K n hK hn hKn j (ry k)]

end Verification
