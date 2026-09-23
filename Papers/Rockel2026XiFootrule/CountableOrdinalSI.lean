import Papers.Rockel2026XiFootrule.CountableOrdinalMixedSI

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.Rockel2026XiFootrule

/-- Replacing every block except one by comonotonic blocks preserves SI. -/
private theorem countable_singleBlock_isSI
    (B : Copula 2) (hB : B.IsSI) (k : ℕ)
    (P : Copula.CountableIntervalPartition) :
    (Copula.countableOrdinalSum P
      (fun j => if j = k then B else Copula.comonotonic 2)).IsSI := by
  induction k generalizing P with
  | zero =>
      rw [countableOrdinal_recursive]
      have he : (fun j : ℕ => if j + 1 = 0 then B else Copula.comonotonic 2) =
          (fun _ => Copula.comonotonic 2) := by
        funext j
        simp
      rw [he, Copula.countableOrdinalSum_comonotonic]
      simpa using ordinalSum_isSI B (Copula.comonotonic 2)
        hB Copula.isSI_comonotonic (P.point 1)
  | succ k ih =>
      rw [countableOrdinal_recursive]
      have he : (fun j : ℕ => if j + 1 = k + 1 then B else Copula.comonotonic 2) =
          (fun j => if j = k then B else Copula.comonotonic 2) := by
        funext j
        simp
      rw [he]
      simpa using ordinalSum_isSI (Copula.comonotonic 2)
        (Copula.countableOrdinalSum (countableTailPartition P)
          (fun j => if j = k then B else Copula.comonotonic 2))
        Copula.isSI_comonotonic (ih (countableTailPartition P)) (P.point 1)

/-- Adjacent countable ordinal sums preserve stochastic increase for arbitrary
SI component copulas, not just independence/comonotonic blocks. -/
theorem countableOrdinal_isSI (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) (hC : ∀ k, (C k).IsSI) :
    (Copula.countableOrdinalSum P C).IsSI := by
  intro a b c v hab hbc
  by_cases hv : v = 1
  · subst v
    simp only [Copula.cdf_two_one_right]
    nlinarith
  have hv1 : (v : ℝ) < 1 := lt_of_le_of_ne v.property.2 (by
    intro h
    apply hv
    apply Subtype.ext
    exact h)
  have hev : ∀ᶠ n : ℕ in atTop, (v : ℝ) < P.point n :=
    P.tendsto_one.eventually (eventually_gt_nhds hv1)
  obtain ⟨n, hn⟩ := hev.exists
  have hex : ∃ k : ℕ, v ≤ P.point (k + 1) :=
    ⟨n, le_of_lt (hn.trans (P.strictMono (Nat.lt_succ_self n)))⟩
  let k := Nat.find hex
  have hR : v ≤ P.point (k + 1) := Nat.find_spec hex
  have hL : P.point k ≤ v := by
    by_cases hk : k = 0
    · simp [hk, P.zero]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hprev : k - 1 < k := by omega
      have hnot : ¬ v ≤ P.point ((k - 1) + 1) := Nat.find_min hex hprev
      have heq : k - 1 + 1 = k := by omega
      rw [heq] at hnot
      exact le_of_not_ge hnot
  have heq (u : I) :
      (Copula.countableOrdinalSum P C).cdf ![u, v] =
        (Copula.countableOrdinalSum P
          (fun j => if j = k then C k else Copula.comonotonic 2)).cdf ![u, v] :=
    countableOrdinal_cdf_section_eq_of_component_eq P C _ k v hL hR (by simp) u
  rw [heq a, heq b, heq c]
  exact countable_singleBlock_isSI (C k) (hC k) k P a b c v hab hbc

/-- SI of an interior binary ordinal sum forces SI in each rescaled component. -/
theorem ordinalSum_isSI_components (C D : Copula 2) (a : I)
    (ha0 : 0 < a) (ha1 : a < 1)
    (h : (C.ordinalSum D a).IsSI) : C.IsSI ∧ D.IsSI := by
  have hp : (0 : ℝ) < a := ha0
  have hq : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
  constructor
  · intro u w x v huw hwx
    have hs := h (Copula.OrdinalSum.lowerEmbed a u)
      (Copula.OrdinalSum.lowerEmbed a w)
      (Copula.OrdinalSum.lowerEmbed a x)
      (Copula.OrdinalSum.lowerEmbed a v)
      (Copula.OrdinalSum.lowerEmbed_mono a huw)
      (Copula.OrdinalSum.lowerEmbed_mono a hwx)
    rw [Copula.cdf_ordinalSum_lowerEmbed C D a x v ha0,
      Copula.cdf_ordinalSum_lowerEmbed C D a u v ha0,
      Copula.cdf_ordinalSum_lowerEmbed C D a w v ha0] at hs
    have hscaled : (a : ℝ) ^ 2 *
        (((w : ℝ) - u) * C.cdf ![x, v] +
          ((x : ℝ) - w) * C.cdf ![u, v]) ≤
        (a : ℝ) ^ 2 * (((x : ℝ) - u) * C.cdf ![w, v]) := by
      simp only [Copula.OrdinalSum.lowerEmbed] at hs
      nlinarith [hs]
    exact (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hp)).mp hscaled
  · intro u w x v huw hwx
    have hs := h (Copula.OrdinalSum.upperEmbed a u)
      (Copula.OrdinalSum.upperEmbed a w)
      (Copula.OrdinalSum.upperEmbed a x)
      (Copula.OrdinalSum.upperEmbed a v)
      (Copula.OrdinalSum.upperEmbed_mono a huw)
      (Copula.OrdinalSum.upperEmbed_mono a hwx)
    rw [Copula.cdf_ordinalSum_upperEmbed C D a x v ha1,
      Copula.cdf_ordinalSum_upperEmbed C D a u v ha1,
      Copula.cdf_ordinalSum_upperEmbed C D a w v ha1] at hs
    have hscaled : (1 - (a : ℝ)) ^ 2 *
        (((w : ℝ) - u) * D.cdf ![x, v] +
          ((x : ℝ) - w) * D.cdf ![u, v]) ≤
        (1 - (a : ℝ)) ^ 2 * (((x : ℝ) - u) * D.cdf ![w, v]) := by
      simp only [Copula.OrdinalSum.upperEmbed] at hs
      nlinarith [hs]
    exact (mul_le_mul_iff_of_pos_left (sq_pos_of_pos hq)).mp hscaled

private theorem countableOrdinal_isSI_tail
    (P : Copula.CountableIntervalPartition) (C : ℕ → Copula 2)
    (h : (Copula.countableOrdinalSum P C).IsSI) (n : ℕ) :
    (Copula.countableOrdinalSum (tailIter P n) (fun k => C (n + k))).IsSI := by
  induction n with
  | zero => simpa [tailIter] using h
  | succ n ih =>
      let Q := tailIter P n
      have h0 : 0 < Q.point 1 := by
        simpa [Q.zero] using Q.strictMono (show (0 : ℕ) < 1 by omega)
      have h1 : Q.point 1 < 1 :=
        (Q.strictMono (Nat.lt_succ_self 1)).trans_le (Q.point 2).property.2
      rw [countableOrdinal_recursive] at ih
      have hparts := ordinalSum_isSI_components (C n)
        (Copula.countableOrdinalSum (countableTailPartition Q) (fun k => C (n + (k + 1))))
        (Q.point 1) h0 h1 (by
          simpa only [Nat.add_zero] using ih)
      have hfun : (fun k : ℕ => C (n + (k + 1))) =
          (fun k => C (n + 1 + k)) := by
        funext k
        congr 1
        omega
      rw [hfun] at hparts
      simpa [tailIter, Q] using hparts.2

/-- For an adjacent countable partition, the sum is SI exactly when every
component is SI. -/
theorem countableOrdinal_isSI_iff (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2) :
    (Copula.countableOrdinalSum P C).IsSI ↔ ∀ k, (C k).IsSI := by
  constructor
  · intro h k
    let Q := tailIter P k
    have h0 : 0 < Q.point 1 := by
      simpa [Q.zero] using Q.strictMono (show (0 : ℕ) < 1 by omega)
    have h1 : Q.point 1 < 1 :=
      (Q.strictMono (Nat.lt_succ_self 1)).trans_le (Q.point 2).property.2
    have htail := countableOrdinal_isSI_tail P C h k
    rw [countableOrdinal_recursive] at htail
    have hparts := ordinalSum_isSI_components (C k)
      (Copula.countableOrdinalSum (countableTailPartition Q) (fun j => C (k + (j + 1))))
      (Q.point 1) h0 h1 (by
        simpa only [Nat.add_zero] using htail)
    exact hparts.1
  · exact countableOrdinal_isSI P C

/-- Symmetry, SI, and rank equality pass from every block to an adjacent
countable ordinal sum. -/
theorem countableOrdinal_symmetric_si_rank_equality
    (P : Copula.CountableIntervalPartition) (C : ℕ → Copula 2)
    (hC : ∀ k, (C k).IsSI ∧ (C k).IsExchangeable ∧
      (C k).chatterjeeXi = (C k).spearmanFootrule) :
    (Copula.countableOrdinalSum P C).IsSI ∧
      (Copula.countableOrdinalSum P C).IsExchangeable ∧
      (Copula.countableOrdinalSum P C).chatterjeeXi =
        (Copula.countableOrdinalSum P C).spearmanFootrule := by
  refine ⟨countableOrdinal_isSI P C (fun k => (hC k).1),
    countableOrdinal_exchangeable P C (fun k => (hC k).2.1), ?_⟩
  exact countableOrdinal_xi_eq_footrule P C (fun k => (hC k).2.2)

end Papers.Rockel2026XiFootrule
