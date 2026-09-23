import Papers.Rockel2026XiFootrule.CountableOrdinalPartial

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.Rockel2026XiFootrule

private theorem countablePoint_lt_one (P : Copula.CountableIntervalPartition) (n : ℕ) :
    P.point n < 1 :=
  (P.strictMono (Nat.lt_succ_self n)).trans_le (P.point (n + 1)).property.2

noncomputable def countableTailPartition (P : Copula.CountableIntervalPartition) :
    Copula.CountableIntervalPartition where
  point k := Copula.OrdinalSum.upperCoord (P.point 1) (P.point (k + 1))
  strictMono := by
    intro i j hij
    have ha : P.point 1 < 1 := countablePoint_lt_one P 1
    have hi : P.point 1 ≤ P.point (i + 1) :=
      P.strictMono.monotone (by omega)
    have hj : P.point 1 ≤ P.point (j + 1) :=
      P.strictMono.monotone (by omega)
    have hp : P.point (i + 1) < P.point (j + 1) :=
      P.strictMono (by omega)
    change (Copula.OrdinalSum.upperCoord (P.point 1) (P.point (i + 1)) : ℝ) <
      (Copula.OrdinalSum.upperCoord (P.point 1) (P.point (j + 1)) : ℝ)
    rw [Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha hi,
      Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha hj]
    have hpR : (P.point (i + 1) : ℝ) < P.point (j + 1) := hp
    exact div_lt_div_of_pos_right (sub_lt_sub_right hpR _) (sub_pos.mpr ha)
  zero := by
    simp [Copula.OrdinalSum.upperCoord_of_le]
  tendsto_one := by
    have hshift : Tendsto (fun k : ℕ => (P.point (k + 1) : ℝ)) atTop (𝓝 1) :=
      P.tendsto_one.comp (tendsto_add_atTop_nat 1)
    have ha : P.point 1 < 1 := countablePoint_lt_one P 1
    have hge (k : ℕ) : P.point 1 ≤ P.point (k + 1) :=
      P.strictMono.monotone (by omega)
    have hlim := (hshift.sub_const (P.point 1 : ℝ)).div_const (1 - (P.point 1 : ℝ))
    have haR : (P.point 1 : ℝ) < 1 := ha
    have htarget : (1 - (P.point 1 : ℝ)) / (1 - (P.point 1 : ℝ)) = 1 := by
      field_simp [(sub_pos.mpr haR).ne']
    rw [htarget] at hlim
    convert hlim using 1
    funext k
    exact (Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha (hge k))

private theorem tailWidth (P : Copula.CountableIntervalPartition) (k : ℕ) :
    (countableTailPartition P).width k =
      P.width (k + 1) / (1 - (P.point 1 : ℝ)) := by
  have ha : P.point 1 < 1 := countablePoint_lt_one P 1
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
private theorem tailCoord (P : Copula.CountableIntervalPartition) (k : ℕ)
    (u : I) :
    (countableTailPartition P).coord k u =
      P.coord (k + 1) (Copula.OrdinalSum.upperEmbed (P.point 1) u) := by
  apply Subtype.ext
  unfold Copula.CountableIntervalPartition.coord
  congr 1
  rw [tailWidth]
  congr 1
  have ha : P.point 1 < 1 := countablePoint_lt_one P 1
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
theorem countablePi_upper_component_tail (P : Copula.CountableIntervalPartition) :
    (Copula.countableOrdinalSumPi P).upperOrdinalComponent (P.point 1)
      (countablePoint_lt_one P 1)
      (countablePi_diagonal_fixed P 1) =
        Copula.countableOrdinalSumPi (countableTailPartition P) := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_upperOrdinalComponent, Copula.cdf_countableOrdinalSumPi,
    Copula.cdf_countableOrdinalSumPi]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  let a : I := P.point 1
  let b : ℝ := 1 - (a : ℝ)
  let Q := countableTailPartition P
  let f : ℕ → ℝ := fun k =>
    P.width k *
      ((P.coord k (Copula.OrdinalSum.upperEmbed a u) : ℝ) *
        P.coord k (Copula.OrdinalSum.upperEmbed a v))
  have hf : Summable f := by
    simpa [f, Copula.cdf_independence, Fin.prod_univ_two] using
      P.summable_cdf (fun _ => Copula.independence 2)
        (Copula.OrdinalSum.upperEmbed a u) (Copula.OrdinalSum.upperEmbed a v)
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
      b * (∑' k, Q.width k * ((Q.coord k u : ℝ) * Q.coord k v)) := by
    have hb : b ≠ 0 := by
      dsimp [b, a]
      exact (sub_pos.mpr (show (P.point 1 : ℝ) < 1 from countablePoint_lt_one P 1)).ne'
    have hw (k : ℕ) : P.width (k + 1) = b * Q.width k := by
      rw [tailWidth]
      dsimp [b, Q, a]
      have hbR : 1 - (P.point 1 : ℝ) ≠ 0 := by simpa [b, a] using hb
      field_simp [hbR]
    have hterm (k : ℕ) :
        f (k + 1) = b * (Q.width k * ((Q.coord k u : ℝ) * Q.coord k v)) := by
      dsimp [f]
      rw [← tailCoord P k u, ← tailCoord P k v, hw]
      ring
    simp_rw [hterm]
    exact tsum_mul_left
  have hseries :
      (∑' k, f k) =
        (a : ℝ) + b * (∑' k, Q.width k * ((Q.coord k u : ℝ) * Q.coord k v)) := by
    rw [hf.tsum_eq_zero_add, hfirst, htail]
  change ((∑' k, f k) - (a : ℝ)) / b =
    ∑' k, Q.width k * ((Q.coord k u : ℝ) * Q.coord k v)
  rw [hseries]
  have hb : b ≠ 0 := by
    dsimp [b, a]
    exact (sub_pos.mpr (show (P.point 1 : ℝ) < 1 from countablePoint_lt_one P 1)).ne'
  field_simp [hb]
  ring
theorem countablePi_recursive (P : Copula.CountableIntervalPartition) :
    Copula.countableOrdinalSumPi P =
      (Copula.independence 2).ordinalSum
        (Copula.countableOrdinalSumPi (countableTailPartition P)) (P.point 1) := by
  have h0 : 0 < P.point 1 := by
    simpa [P.zero] using P.strictMono (show (0 : ℕ) < 1 by omega)
  have h1 : P.point 1 < 1 := countablePoint_lt_one P 1
  let C := Copula.countableOrdinalSumPi P
  have hf : C.diagonal (P.point 1) = P.point 1 :=
    countablePi_diagonal_fixed P 1
  calc
    C = (C.lowerOrdinalComponent (P.point 1) h0 hf).ordinalSum
      (C.upperOrdinalComponent (P.point 1) h1 hf) (P.point 1) :=
        (C.ordinalSum_components (P.point 1) h0 h1 hf).symm
    _ = _ := by
      rw [countablePi_first_lower_component P, countablePi_upper_component_tail P]
theorem countablePi_gap_recursive (P : Copula.CountableIntervalPartition) :
    (Copula.countableOrdinalSumPi P).chatterjeeXi -
      (Copula.countableOrdinalSumPi P).spearmanFootrule =
      (1 - (P.point 1 : ℝ)) ^ 2 *
        ((Copula.countableOrdinalSumPi (countableTailPartition P)).chatterjeeXi -
          (Copula.countableOrdinalSumPi (countableTailPartition P)).spearmanFootrule) := by
  rw [countablePi_recursive, Verification.chatterjeeXi_ordinalSum,
    Copula.spearmanFootrule_ordinalSum, Copula.chatterjeeXi_independence,
    Copula.spearmanFootrule_independence]
  ring

noncomputable def tailIter (P : Copula.CountableIntervalPartition) : ℕ → Copula.CountableIntervalPartition
  | 0 => P
  | n + 1 => countableTailPartition (tailIter P n)

private theorem tailIter_point (P : Copula.CountableIntervalPartition) (n k : ℕ) :
    ((tailIter P n).point k : ℝ) =
      ((P.point (n + k) : ℝ) - P.point n) / (1 - (P.point n : ℝ)) := by
  induction n generalizing k with
  | zero =>
      simp [tailIter, P.zero]
  | succ n ih =>
      have ha : (tailIter P n).point 1 < 1 :=
        countablePoint_lt_one (tailIter P n) 1
      have hge : (tailIter P n).point 1 ≤ (tailIter P n).point (k + 1) :=
        (tailIter P n).strictMono.monotone (by omega)
      change (Copula.OrdinalSum.upperCoord ((tailIter P n).point 1)
        ((tailIter P n).point (k + 1)) : ℝ) = _
      rw [Copula.OrdinalSum.coe_upperCoord_of_ge _ _ ha hge,
        ih 1, ih (k + 1)]
      have hn : (P.point n : ℝ) < 1 := countablePoint_lt_one P n
      have hnext : (P.point (n + 1) : ℝ) < 1 :=
        countablePoint_lt_one P (n + 1)
      have hdn : 1 - (P.point n : ℝ) ≠ 0 := (sub_pos.mpr hn).ne'
      have hds : 1 - (P.point (n + 1) : ℝ) ≠ 0 := (sub_pos.mpr hnext).ne'
      have hindex : n + (k + 1) = n + 1 + k := by omega
      rw [hindex]
      field_simp [hdn, hds]
      ring
private theorem countablePi_gap_iter (P : Copula.CountableIntervalPartition) (n : ℕ) :
    (Copula.countableOrdinalSumPi P).chatterjeeXi -
      (Copula.countableOrdinalSumPi P).spearmanFootrule =
      (1 - (P.point n : ℝ)) ^ 2 *
        ((Copula.countableOrdinalSumPi (tailIter P n)).chatterjeeXi -
          (Copula.countableOrdinalSumPi (tailIter P n)).spearmanFootrule) := by
  induction n with
  | zero =>
      simp [tailIter, P.zero]
  | succ n ih =>
      rw [countablePi_gap_recursive (tailIter P n)] at ih
      rw [ih]
      change (1 - (P.point n : ℝ)) ^ 2 *
        ((1 - ((tailIter P n).point 1 : ℝ)) ^ 2 *
          ((Copula.countableOrdinalSumPi (tailIter P (n + 1))).chatterjeeXi -
            (Copula.countableOrdinalSumPi (tailIter P (n + 1))).spearmanFootrule)) =
        (1 - (P.point (n + 1) : ℝ)) ^ 2 *
          ((Copula.countableOrdinalSumPi (tailIter P (n + 1))).chatterjeeXi -
            (Copula.countableOrdinalSumPi (tailIter P (n + 1))).spearmanFootrule)
      rw [tailIter_point P n 1]
      have hn : (P.point n : ℝ) < 1 := countablePoint_lt_one P n
      have hdn : 1 - (P.point n : ℝ) ≠ 0 := (sub_pos.mpr hn).ne'
      have hindex : n + 1 = n + 1 := rfl
      field_simp [hdn]
      ring
theorem countablePi_xi_eq_footrule (P : Copula.CountableIntervalPartition) :
    (Copula.countableOrdinalSumPi P).chatterjeeXi =
      (Copula.countableOrdinalSumPi P).spearmanFootrule := by
  let gap : ℝ := (Copula.countableOrdinalSumPi P).chatterjeeXi -
    (Copula.countableOrdinalSumPi P).spearmanFootrule
  have hbound (n : ℕ) :
      |(Copula.countableOrdinalSumPi (tailIter P n)).chatterjeeXi -
        (Copula.countableOrdinalSumPi (tailIter P n)).spearmanFootrule| ≤ 2 := by
    have hxi := (Copula.countableOrdinalSumPi (tailIter P n)).chatterjeeXi_mem_Icc
    have hfo := (Copula.countableOrdinalSumPi (tailIter P n)).spearmanFootrule_mem_Icc
    rcases hxi with ⟨hxi0, hxi1⟩
    rcases hfo with ⟨hfo0, hfo1⟩
    rw [abs_le]
    constructor <;> linarith
  have hle (n : ℕ) : |gap| ≤ 2 * (1 - (P.point n : ℝ)) ^ 2 := by
    have hiter := countablePi_gap_iter P n
    change gap = _ at hiter
    rw [hiter, abs_mul, abs_of_nonneg (sq_nonneg _)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hbound n) (sq_nonneg (1 - (P.point n : ℝ)))
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * (1 - (P.point n : ℝ)) ^ 2)
      Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun n : ℕ => 1 - (P.point n : ℝ))
        Filter.atTop (nhds 0) := by
      convert P.tendsto_one.const_sub 1 using 1; norm_num
    convert (hsub.pow 2).const_mul 2 using 1; norm_num
  have hzero : |gap| ≤ 0 := ge_of_tendsto' hlim hle
  have : gap = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  exact sub_eq_zero.mp this
end Papers.Rockel2026XiFootrule