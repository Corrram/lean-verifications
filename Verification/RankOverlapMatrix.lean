import Verification.RankCopula

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval BigOperators

namespace Verification

/-- Lebesgue overlap of two half-open cells, with the paper's Ico convention. -/
noncomputable def cellOverlap {m n : ℕ} (P : IntervalPartition m) (Q : IntervalPartition n)
    (i : Fin m) (j : Fin n) : ℝ :=
  (volume : Measure I).real (Ico (P.point i.castSucc) (P.point i.succ) ∩ Ico (Q.point j.castSucc) (Q.point j.succ))

theorem cellOverlap_formula {m n : ℕ} (P : IntervalPartition m) (Q : IntervalPartition n)
    (i : Fin m) (j : Fin n) :
    cellOverlap P Q i j=Q.width j*((Q.coord j (P.point i.succ) : ℝ)-(Q.coord j (P.point i.castSucc) : ℝ)) := by
  unfold cellOverlap Measure.real
  rw [Ico_inter_Ico,unitInterval.volume_Ico,ENNReal.toReal_ofReal',mul_sub,Q.width_mul_coord,Q.width_mul_coord]
  have hP : (P.point i.castSucc : ℝ)≤P.point i.succ := (P.strictMono Fin.castSucc_lt_succ).le
  have hQ : (Q.point j.castSucc : ℝ)≤Q.point j.succ := (Q.strictMono Fin.castSucc_lt_succ).le
  change max (min (P.point i.succ : ℝ) (Q.point j.succ)-max (P.point i.castSucc : ℝ) (Q.point j.castSucc)) 0 = _
  grind

/-- Exact fractional rank-binning matrix in the paper, for arbitrary coarse partitions. -/
theorem rankCopula_cellMass {m r n : ℕ} (hn : 0<n) (rx ry : Equiv.Perm (Fin n))
    (P : IntervalPartition m) (Q : IntervalPartition r) (i : Fin m) (j : Fin r) :
    ((rankCopula n hn rx ry).cellMass P Q).mass i j = (n : ℝ)*∑ k,
      cellOverlap P (IntervalPartition.uniform n hn) i (rx k)*
      cellOverlap Q (IntervalPartition.uniform n hn) j (ry k) := by
  change (rankCopula n hn rx ry).cdf ![P.point i.succ,Q.point j.succ]-
    (rankCopula n hn rx ry).cdf ![P.point i.castSucc,Q.point j.succ]-
    (rankCopula n hn rx ry).cdf ![P.point i.succ,Q.point j.castSucc]+
    (rankCopula n hn rx ry).cdf ![P.point i.castSucc,Q.point j.castSucc] = _
  simp only [rankCopula_cdf,cellOverlap_formula,IntervalPartition.width_uniform,Finset.mul_sum]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hnR : (n : ℝ)≠0 := (Nat.cast_pos.mpr hn).ne'
  field_simp
  ring

end Verification
