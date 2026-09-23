import Papers.Rockel2026XiFootrule.CountableOrdinalTail

open ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- Countable ordinal sums inherit exchangeability from every block. -/
theorem countableOrdinal_exchangeable (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) (hC : ∀ k, (C k).IsExchangeable) :
    (Copula.countableOrdinalSum P C).IsExchangeable := by
  apply (Copula.isExchangeable_iff _).mpr
  intro u v
  simp only [Copula.cdf_countableOrdinalSum, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  ext k
  exact congrArg (fun x : ℝ => P.width k * x)
    ((Copula.isExchangeable_iff _).mp (hC k) _ _)

/-- Every countable ordinal-sum partition endpoint is a diagonal fixed point. -/
theorem countableOrdinal_diagonal_fixed (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) (n : ℕ) :
    (Copula.countableOrdinalSum P C).diagonal (P.point n) = P.point n := by
  have hc (k : ℕ) : (C k).cdf ![P.coord k (P.point n), P.coord k (P.point n)] =
      (P.coord k (P.point n) : ℝ) := by
    by_cases h : k < n
    · have hkn : k + 1 ≤ n := by omega
      rw [P.coord_of_ge k (P.point n) (P.strictMono.monotone hkn)]
      simp
    · have hnk : n ≤ k := Nat.le_of_not_gt h
      rw [P.coord_of_le k (P.point n) (P.strictMono.monotone hnk)]
      simp
  change (Copula.countableOrdinalSum P C).cdf ![P.point n, P.point n] =
    (P.point n : ℝ)
  rw [Copula.cdf_countableOrdinalSum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [hc]
  exact (P.hasSum_width_mul_coord (P.point n)).tsum_eq

/-- Every positive countable partition endpoint gives an actual binary split. -/
theorem countableOrdinal_has_binary_split (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) (n : ℕ) :
    ∃ D E : Copula 2, D.ordinalSum E (P.point (n + 1)) =
      Copula.countableOrdinalSum P C := by
  have h0 : 0 < P.point (n + 1) := by
    simpa [P.zero] using P.strictMono (Nat.zero_lt_succ n)
  have h1 : P.point (n + 1) < 1 :=
    (P.strictMono (Nat.lt_succ_self (n + 1))).trans_le
      (P.point (n + 2)).property.2
  exact ((Copula.countableOrdinalSum P C).diagonal_eq_iff_exists_ordinalSum
    (P.point (n + 1)) h0 h1).mp (countableOrdinal_diagonal_fixed P C (n + 1))

private theorem countableOrdinal_first_coord (P : Copula.CountableIntervalPartition)
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

/-- The first rescaled component of an arbitrary adjacent countable sum is its first block. -/
theorem countableOrdinal_first_lower_component (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) :
    (Copula.countableOrdinalSum P C).lowerOrdinalComponent (P.point 1)
      (by simpa [P.zero] using P.strictMono (show (0 : ℕ) < 1 by omega))
      (countableOrdinal_diagonal_fixed P C 1) = C 0 := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_lowerOrdinalComponent, Copula.cdf_countableOrdinalSum]
  have ha : 0 < P.point 1 := by
    simpa [P.zero] using P.strictMono (show (0 : ℕ) < 1 by omega)
  have hz (k : ℕ) (hk : k ≠ 0) (t : I) :
      P.coord k (Copula.OrdinalSum.lowerEmbed (P.point 1) t) = 0 := by
    have hle : 1 ≤ k := by omega
    exact P.coord_of_le k _ ((Copula.OrdinalSum.lowerEmbed_le _ _).trans
      (P.strictMono.monotone hle))
  have hs :
      (∑' k, P.width k *
        (C k).cdf ![P.coord k (Copula.OrdinalSum.lowerEmbed (P.point 1) u),
          P.coord k (Copula.OrdinalSum.lowerEmbed (P.point 1) v)]) =
      P.width 0 *
        (C 0).cdf ![P.coord 0 (Copula.OrdinalSum.lowerEmbed (P.point 1) u),
          P.coord 0 (Copula.OrdinalSum.lowerEmbed (P.point 1) v)] := by
    apply tsum_eq_single 0
    intro k hk
    rw [hz k hk u]
    simp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hs, countableOrdinal_first_coord P u, countableOrdinal_first_coord P v]
  have hw : P.width 0 = (P.point 1 : ℝ) := by
    change (P.point 1 : ℝ) - P.point 0 = _
    rw [P.zero]
    norm_num
  rw [hw]
  field_simp [(show (P.point 1 : ℝ) ≠ 0 from ne_of_gt ha)]

private theorem generalPoint_lt_one (P : Copula.CountableIntervalPartition) (n : ℕ) :
    P.point n < 1 :=
  (P.strictMono (Nat.lt_succ_self n)).trans_le (P.point (n + 1)).property.2

private theorem generalTailWidth (P : Copula.CountableIntervalPartition) (k : ℕ) :
    (countableTailPartition P).width k =
      P.width (k + 1) / (1 - (P.point 1 : ℝ)) := by
  have ha : P.point 1 < 1 := generalPoint_lt_one P 1
  have h1 : P.point 1 ≤ P.point (k + 1) :=
    P.strictMono.monotone (by omega)
  have h2 : P.point 1 ≤ P.point (k + 2) :=
    P.strictMono.monotone (by omega)
  change (Copula.OrdinalSum.upperCoord (P.point 1) (P.point (k + 2)) : ℝ) -
    (Copula.OrdinalSum.upperCoord (P.point 1) (P.point (k + 1)) : ℝ) =
      ((P.point (k + 2) : ℝ) - P.point (k + 1)) / (1 - (P.point 1 : ℝ))
  rw [Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha h2,
    Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha h1]
  ring
private theorem generalTailCoord (P : Copula.CountableIntervalPartition) (k : ℕ)
    (u : I) :
    (countableTailPartition P).coord k u =
      P.coord (k + 1) (Copula.OrdinalSum.upperEmbed (P.point 1) u) := by
  apply Subtype.ext
  unfold Copula.CountableIntervalPartition.coord
  congr 1
  rw [generalTailWidth]
  congr 1
  have ha : P.point 1 < 1 := generalPoint_lt_one P 1
  have hge : P.point 1 ≤ P.point (k + 1) :=
    P.strictMono.monotone (by omega)
  change ((u : ℝ) -
      (Copula.OrdinalSum.upperCoord (P.point 1) (P.point (k + 1)) : ℝ)) /
      (P.width (k + 1) / (1 - (P.point 1 : ℝ))) =
    ((Copula.OrdinalSum.upperEmbed (P.point 1) u : ℝ) - P.point (k + 1)) /
      P.width (k + 1)
  rw [Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha hge]
  have hd : P.width (k + 1) ≠ 0 := (P.width_pos (k + 1)).ne'
  have haR : (P.point 1 : ℝ) < 1 := ha
  have hb : 1 - (P.point 1 : ℝ) ≠ 0 := (sub_pos.mpr haR).ne'
  change ((u : ℝ) - ((P.point (k + 1) : ℝ) - P.point 1) /
      (1 - (P.point 1 : ℝ))) / (P.width (k + 1) / (1 - (P.point 1 : ℝ))) =
    ((P.point 1 : ℝ) + (1 - (P.point 1 : ℝ)) * u - P.point (k + 1)) /
      P.width (k + 1)
  field_simp [hd, hb]
  ring
/-- The remaining rescaled component is the shifted countable sum. -/
theorem countableOrdinal_upper_component_tail (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) :
    (Copula.countableOrdinalSum P C).upperOrdinalComponent (P.point 1)
      (generalPoint_lt_one P 1)
      (countableOrdinal_diagonal_fixed P C 1) =
        Copula.countableOrdinalSum (countableTailPartition P) (fun k => C (k + 1)) := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_upperOrdinalComponent, Copula.cdf_countableOrdinalSum,
    Copula.cdf_countableOrdinalSum]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  let a : I := P.point 1
  let b : ℝ := 1 - (a : ℝ)
  let Q := countableTailPartition P
  let f : ℕ → ℝ := fun k =>
    P.width k *
      (C k).cdf ![P.coord k (Copula.OrdinalSum.upperEmbed a u),
        P.coord k (Copula.OrdinalSum.upperEmbed a v)]
  have hf : Summable f := by
    simpa [f] using
      P.summable_cdf C (Copula.OrdinalSum.upperEmbed a u)
        (Copula.OrdinalSum.upperEmbed a v)
  have hfirst : f 0 = (a : ℝ) := by
    have hu : P.coord 0 (Copula.OrdinalSum.upperEmbed a u) = 1 :=
      P.coord_of_ge 0 _ (Copula.OrdinalSum.le_upperEmbed _ _)
    have hv : P.coord 0 (Copula.OrdinalSum.upperEmbed a v) = 1 :=
      P.coord_of_ge 0 _ (Copula.OrdinalSum.le_upperEmbed _ _)
    have hw : P.width 0 = (a : ℝ) := by
      change (P.point 1 : ℝ) - P.point 0 = _
      rw [P.zero]
      norm_num
      rfl
    simp [f, a, hu, hv, hw]
  have htail : (∑' k, f (k + 1)) =
      b * (∑' k, Q.width k *
        (C (k + 1)).cdf ![Q.coord k u, Q.coord k v]) := by
    have hb : b ≠ 0 := by
      dsimp [b, a]
      exact (sub_pos.mpr (show (P.point 1 : ℝ) < 1 from generalPoint_lt_one P 1)).ne'
    have hw (k : ℕ) : P.width (k + 1) = b * Q.width k := by
      rw [generalTailWidth]
      dsimp [b, Q, a]
      have hbR : 1 - (P.point 1 : ℝ) ≠ 0 := by simpa [b, a] using hb
      field_simp [hbR]
    have hterm (k : ℕ) :
        f (k + 1) = b * (Q.width k *
          (C (k + 1)).cdf ![Q.coord k u, Q.coord k v]) := by
      dsimp [f]
      rw [← generalTailCoord P k u, ← generalTailCoord P k v, hw]
      ring
    simp_rw [hterm]
    exact tsum_mul_left
  have hseries :
      (∑' k, f k) =
        (a : ℝ) + b * (∑' k, Q.width k *
          (C (k + 1)).cdf ![Q.coord k u, Q.coord k v]) := by
    rw [hf.tsum_eq_zero_add, hfirst, htail]
  change ((∑' k, f k) - (a : ℝ)) / b =
    ∑' k, Q.width k * (C (k + 1)).cdf ![Q.coord k u, Q.coord k v]
  rw [hseries]
  have hb : b ≠ 0 := by
    dsimp [b, a]
    exact (sub_pos.mpr (show (P.point 1 : ℝ) < 1 from generalPoint_lt_one P 1)).ne'
  field_simp [hb]
  ring

/-- Canonical binary recursion for arbitrary adjacent countable ordinal sums. -/
theorem countableOrdinal_recursive (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) :
    Copula.countableOrdinalSum P C =
      (C 0).ordinalSum
        (Copula.countableOrdinalSum (countableTailPartition P) (fun k => C (k + 1)))
        (P.point 1) := by
  have h0 : 0 < P.point 1 := by
    simpa [P.zero] using P.strictMono (show (0 : ℕ) < 1 by omega)
  have h1 : P.point 1 < 1 := generalPoint_lt_one P 1
  let S := Copula.countableOrdinalSum P C
  have hf : S.diagonal (P.point 1) = P.point 1 :=
    countableOrdinal_diagonal_fixed P C 1
  calc
    S = (S.lowerOrdinalComponent (P.point 1) h0 hf).ordinalSum
      (S.upperOrdinalComponent (P.point 1) h1 hf) (P.point 1) :=
        (S.ordinalSum_components (P.point 1) h0 h1 hf).symm
    _ = _ := by
      rw [countableOrdinal_first_lower_component P C,
        countableOrdinal_upper_component_tail P C]

/-- The rank-coefficient gap contracts by the square of the tail width. -/
theorem countableOrdinal_gap_recursive (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) :
    (Copula.countableOrdinalSum P C).chatterjeeXi -
      (Copula.countableOrdinalSum P C).spearmanFootrule =
      (P.point 1 : ℝ) ^ 2 * ((C 0).chatterjeeXi - (C 0).spearmanFootrule) +
      (1 - (P.point 1 : ℝ)) ^ 2 *
        ((Copula.countableOrdinalSum (countableTailPartition P) (fun k => C (k + 1))).chatterjeeXi -
          (Copula.countableOrdinalSum (countableTailPartition P) (fun k => C (k + 1))).spearmanFootrule) := by
  rw [countableOrdinal_recursive, Verification.chatterjeeXi_ordinalSum,
    Copula.spearmanFootrule_ordinalSum]
  ring

private theorem generalTailIter_point (P : Copula.CountableIntervalPartition) (n k : ℕ) :
    ((tailIter P n).point k : ℝ) =
      ((P.point (n + k) : ℝ) - P.point n) / (1 - (P.point n : ℝ)) := by
  induction n generalizing k with
  | zero =>
      simp [tailIter, P.zero]
  | succ n ih =>
      have ha : (tailIter P n).point 1 < 1 :=
        generalPoint_lt_one (tailIter P n) 1
      have hge : (tailIter P n).point 1 ≤ (tailIter P n).point (k + 1) :=
        (tailIter P n).strictMono.monotone (by omega)
      change (Copula.OrdinalSum.upperCoord ((tailIter P n).point 1)
        ((tailIter P n).point (k + 1)) : ℝ) = _
      rw [Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha hge,
        ih 1, ih (k + 1)]
      have hn : (P.point n : ℝ) < 1 := generalPoint_lt_one P n
      have hnext : (P.point (n + 1) : ℝ) < 1 :=
        generalPoint_lt_one P (n + 1)
      have hdn : 1 - (P.point n : ℝ) ≠ 0 := (sub_pos.mpr hn).ne'
      have hds : 1 - (P.point (n + 1) : ℝ) ≠ 0 := (sub_pos.mpr hnext).ne'
      have hindex : n + (k + 1) = n + 1 + k := by omega
      rw [hindex]
      field_simp [hdn, hds]
      ring
private theorem countableOrdinal_gap_iter (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2)
    (hC : ∀ k, (C k).chatterjeeXi = (C k).spearmanFootrule)
    (n : ℕ) :
    (Copula.countableOrdinalSum P C).chatterjeeXi -
      (Copula.countableOrdinalSum P C).spearmanFootrule =
      (1 - (P.point n : ℝ)) ^ 2 *
        ((Copula.countableOrdinalSum (tailIter P n) (fun k => C (n + k))).chatterjeeXi -
          (Copula.countableOrdinalSum (tailIter P n) (fun k => C (n + k))).spearmanFootrule) := by
  induction n with
  | zero =>
      simp [tailIter, P.zero]
  | succ n ih =>
      have hstep := countableOrdinal_gap_recursive (tailIter P n) (fun k => C (n + k))
      have hzero : (C n).chatterjeeXi - (C n).spearmanFootrule = 0 :=
        sub_eq_zero.mpr (hC n)
      simp only [zero_add, mul_zero, Nat.add_zero, hzero] at hstep
      rw [hstep] at ih
      rw [ih]
      have hfun : (fun k : ℕ => C (n + (k + 1))) =
          (fun k => C (n + 1 + k)) := by
        funext k
        congr 1
        omega
      rw [hfun]
      change (1 - (P.point n : ℝ)) ^ 2 *
        ((1 - ((tailIter P n).point 1 : ℝ)) ^ 2 *
          ((Copula.countableOrdinalSum (tailIter P (n + 1))
              (fun k => C (n + 1 + k))).chatterjeeXi -
            (Copula.countableOrdinalSum (tailIter P (n + 1))
              (fun k => C (n + 1 + k))).spearmanFootrule)) =
        (1 - (P.point (n + 1) : ℝ)) ^ 2 *
          ((Copula.countableOrdinalSum (tailIter P (n + 1))
              (fun k => C (n + 1 + k))).chatterjeeXi -
            (Copula.countableOrdinalSum (tailIter P (n + 1))
              (fun k => C (n + 1 + k))).spearmanFootrule)
      rw [generalTailIter_point P n 1]
      have hn : (P.point n : ℝ) < 1 := generalPoint_lt_one P n
      have hdn : 1 - (P.point n : ℝ) ≠ 0 := (sub_pos.mpr hn).ne'
      field_simp [hdn]
      ring

/-- Any adjacent countable ordinal sum of rank-equality blocks again has ξ=ψ. -/
theorem countableOrdinal_xi_eq_footrule (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2)
    (hC : ∀ k, (C k).chatterjeeXi = (C k).spearmanFootrule) :
    (Copula.countableOrdinalSum P C).chatterjeeXi =
      (Copula.countableOrdinalSum P C).spearmanFootrule := by
  let gap : ℝ := (Copula.countableOrdinalSum P C).chatterjeeXi -
    (Copula.countableOrdinalSum P C).spearmanFootrule
  have hbound (n : ℕ) :
      |(Copula.countableOrdinalSum (tailIter P n) (fun k => C (n + k))).chatterjeeXi -
        (Copula.countableOrdinalSum (tailIter P n) (fun k => C (n + k))).spearmanFootrule| ≤ 2 := by
    have hxi := (Copula.countableOrdinalSum (tailIter P n) (fun k => C (n + k))).chatterjeeXi_mem_Icc
    have hfo := (Copula.countableOrdinalSum (tailIter P n) (fun k => C (n + k))).spearmanFootrule_mem_Icc
    rcases hxi with ⟨hxi0, hxi1⟩
    rcases hfo with ⟨hfo0, hfo1⟩
    rw [abs_le]
    constructor <;> linarith
  have hle (n : ℕ) : |gap| ≤ 2 * (1 - (P.point n : ℝ)) ^ 2 := by
    have hiter := countableOrdinal_gap_iter P C hC n
    change gap = _ at hiter
    rw [hiter, abs_mul, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound n)
      (sq_nonneg (1 - (P.point n : ℝ)))
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * (1 - (P.point n : ℝ)) ^ 2)
      Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun n : ℕ => 1 - (P.point n : ℝ))
        Filter.atTop (nhds 0) := by
      convert P.tendsto_one.const_sub 1 using 1; norm_num
    convert (hsub.pow 2).const_mul 2 using 1; norm_num
  have hzero : |gap| ≤ 0 := ge_of_tendsto' hlim hle
  have : gap = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  exact sub_eq_zero.mp this

/-- Any adjacent countable sequence of Π and M blocks is symmetric with ξ=ψ. -/
theorem countablePiM_symmetric_rank_equality (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2)
    (hC : ∀ k, C k = Copula.independence 2 ∨ C k = Copula.comonotonic 2) :
    (Copula.countableOrdinalSum P C).IsExchangeable ∧
      (Copula.countableOrdinalSum P C).chatterjeeXi =
        (Copula.countableOrdinalSum P C).spearmanFootrule := by
  constructor
  · apply countableOrdinal_exchangeable P C
    intro k
    rcases hC k with hk | hk
    · simpa [hk] using Copula.isExchangeable_independence
    · simpa [hk] using Copula.isExchangeable_comonotonic
  · apply countableOrdinal_xi_eq_footrule P C
    intro k
    rcases hC k with hk | hk <;> simp [hk]

end Papers.Rockel2026XiFootrule
