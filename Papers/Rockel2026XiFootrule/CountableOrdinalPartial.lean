import Papers.Rockel2026XiFootrule.SymmetricOrdinalSI
import Copula.OrdinalSum.CountableSI
import Copula.OrdinalSum.Decomposition

open ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- Adjacent countable ordinal sums of independence blocks remain symmetric. -/
theorem countablePi_exchangeable (P : Copula.CountableIntervalPartition) :
    (Copula.countableOrdinalSumPi P).IsExchangeable := by
  apply (Copula.isExchangeable_iff _).mpr
  intro u v
  simp only [Copula.cdf_countableOrdinalSumPi]
  congr 1
  ext k
  ring_nf

/-- Every partition endpoint is a diagonal fixed point of the countable sum. -/
theorem countablePi_diagonal_fixed (P : Copula.CountableIntervalPartition)
    (n : ℕ) :
    (Copula.countableOrdinalSumPi P).diagonal (P.point n) = P.point n :=
  Copula.countableOrdinalSumPi_diagonal_fixed P n
/-- Every positive endpoint determines a genuine binary ordinal-sum decomposition. -/
theorem countablePi_has_binary_split (P : Copula.CountableIntervalPartition)
    (n : ℕ) :
    ∃ C D : Copula 2,
      C.ordinalSum D (P.point (n + 1)) = Copula.countableOrdinalSumPi P := by
  have h0 : 0 < P.point (n + 1) := by
    simpa [P.zero] using P.strictMono (Nat.zero_lt_succ n)
  have h1 : P.point (n + 1) < 1 :=
    (P.strictMono (Nat.lt_succ_self (n + 1))).trans_le
      (P.point (n + 2)).property.2
  exact ((Copula.countableOrdinalSumPi P).diagonal_eq_iff_exists_ordinalSum
    (P.point (n + 1)) h0 h1).mp (countablePi_diagonal_fixed P (n + 1))

private theorem countablePi_first_coord (P : Copula.CountableIntervalPartition)
    (u : I) :
    P.coord 0 (Copula.OrdinalSum.lowerEmbed (P.point 1) u) = u := by
  have h0 : 0 < P.point 1 := by
    simpa [P.zero] using P.strictMono (show (0 : ℕ) < 1 by omega)
  apply Subtype.ext
  have hl : P.point 0 ≤ Copula.OrdinalSum.lowerEmbed (P.point 1) u := by
    rw [P.zero]
    exact (Copula.OrdinalSum.lowerEmbed (P.point 1) u).property.1
  have hr : Copula.OrdinalSum.lowerEmbed (P.point 1) u ≤ P.point 1 :=
    Copula.OrdinalSum.lowerEmbed_le _ _
  have hw : P.width 0 = (P.point 1 : ℝ) := by
    change (P.point 1 : ℝ) - P.point 0 = _
    rw [P.zero]
    norm_num
  have he := P.width_mul_coord 0 (Copula.OrdinalSum.lowerEmbed (P.point 1) u)
  rw [hw, P.zero] at he
  have hz : ((0 : I) : ℝ) = 0 := rfl
  rw [hz, min_eq_left (show (Copula.OrdinalSum.lowerEmbed (P.point 1) u : ℝ) ≤ P.point 1 from hr),
    min_eq_right (show (0 : ℝ) ≤ Copula.OrdinalSum.lowerEmbed (P.point 1) u from
      (Copula.OrdinalSum.lowerEmbed (P.point 1) u).property.1)] at he
  apply mul_left_cancel₀ (ne_of_gt (show (0 : ℝ) < P.point 1 from h0))
  simpa [Copula.OrdinalSum.lowerEmbed] using he

/-- The first rescaled component of a countable Pi-block sum is exactly Pi. -/
theorem countablePi_first_lower_component (P : Copula.CountableIntervalPartition) :
    (Copula.countableOrdinalSumPi P).lowerOrdinalComponent (P.point 1)
      (by simpa [P.zero] using P.strictMono (show (0 : ℕ) < 1 by omega))
      (countablePi_diagonal_fixed P 1) = Copula.independence 2 := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_lowerOrdinalComponent, Copula.cdf_countableOrdinalSumPi]
  have ha : 0 < P.point 1 := by
    simpa [P.zero] using P.strictMono (show (0 : ℕ) < 1 by omega)
  have hz (k : ℕ) (hk : k ≠ 0) (t : I) :
      P.coord k (Copula.OrdinalSum.lowerEmbed (P.point 1) t) = 0 := by
    have hle : 1 ≤ k := by omega
    exact P.coord_of_le k _ ((Copula.OrdinalSum.lowerEmbed_le _ _).trans
      (P.strictMono.monotone hle))
  have hs :
      (∑' k, P.width k *
        ((P.coord k (Copula.OrdinalSum.lowerEmbed (P.point 1) u) : ℝ) *
          P.coord k (Copula.OrdinalSum.lowerEmbed (P.point 1) v))) =
      P.width 0 *
        ((P.coord 0 (Copula.OrdinalSum.lowerEmbed (P.point 1) u) : ℝ) *
          P.coord 0 (Copula.OrdinalSum.lowerEmbed (P.point 1) v)) := by
    apply tsum_eq_single 0
    intro k hk
    rw [hz k hk u]
    simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hs, countablePi_first_coord P u, countablePi_first_coord P v,
    Copula.cdf_independence, Fin.prod_univ_two]
  have hw : P.width 0 = (P.point 1 : ℝ) := by
    change (P.point 1 : ℝ) - P.point 0 = _
    rw [P.zero]
    norm_num
  rw [hw]
  field_simp [(show (P.point 1 : ℝ) ≠ 0 from ne_of_gt ha)]
  simp

end Papers.Rockel2026XiFootrule