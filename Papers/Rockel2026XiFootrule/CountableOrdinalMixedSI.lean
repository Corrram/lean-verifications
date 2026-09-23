import Papers.Rockel2026XiFootrule.CountableOrdinalGeneral

open ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.Rockel2026XiFootrule

/-- At a threshold inside one partition block, the CDF section depends only on
that block's component. -/
theorem countableOrdinal_cdf_section_eq_of_component_eq
    (P : Copula.CountableIntervalPartition) (C D : ℕ → Copula 2)
    (k : ℕ) (v : I) (hl : P.point k ≤ v) (hr : v ≤ P.point (k + 1))
    (hk : C k = D k) (u : I) :
    (Copula.countableOrdinalSum P C).cdf ![u, v] =
      (Copula.countableOrdinalSum P D).cdf ![u, v] := by
  simp only [Copula.cdf_countableOrdinalSum, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  congr 1
  ext j
  rcases lt_trichotomy j k with hj | rfl | hj
  · have hge : P.point (j + 1) ≤ v :=
      (P.strictMono.monotone (by omega)).trans hl
    rw [P.coord_of_ge j v hge]
    simp
  · simp [hk]
  · have hle : v ≤ P.point j :=
      hr.trans (P.strictMono.monotone (by omega))
    rw [P.coord_of_le j v hle]
    simp

/-- A countable adjacent sum of independence and comonotonic blocks is SI. -/
theorem countablePiM_isSI (P : Copula.CountableIntervalPartition)
    (C : ℕ → Copula 2)
    (hC : ∀ k, C k = Copula.independence 2 ∨ C k = Copula.comonotonic 2) :
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
  rcases hC k with hk | hk
  · have heq (u : I) :
        (Copula.countableOrdinalSum P C).cdf ![u, v] =
          (Copula.countableOrdinalSumPi P).cdf ![u, v] := by
      simpa [Copula.countableOrdinalSumPi] using
        countableOrdinal_cdf_section_eq_of_component_eq P C
          (fun _ => Copula.independence 2) k v hL hR hk u
    rw [heq a, heq b, heq c]
    exact countablePi_isSI P a b c v hab hbc
  · have heq (u : I) :
        (Copula.countableOrdinalSum P C).cdf ![u, v] =
          (Copula.comonotonic 2).cdf ![u, v] := by
      rw [← Copula.countableOrdinalSum_comonotonic P]
      exact countableOrdinal_cdf_section_eq_of_component_eq P C
        (fun _ => Copula.comonotonic 2) k v hL hR hk u
    rw [heq a, heq b, heq c]
    exact Copula.isSI_comonotonic a b c v hab hbc

/-- Adjacent countable Π/M blocks realize symmetric SI equality cases. -/
theorem countablePiM_symmetric_si_rank_equality
    (P : Copula.CountableIntervalPartition) (C : ℕ → Copula 2)
    (hC : ∀ k, C k = Copula.independence 2 ∨ C k = Copula.comonotonic 2) :
    (Copula.countableOrdinalSum P C).IsSI ∧
      (Copula.countableOrdinalSum P C).IsExchangeable ∧
      (Copula.countableOrdinalSum P C).chatterjeeXi =
        (Copula.countableOrdinalSum P C).spearmanFootrule :=
  ⟨countablePiM_isSI P C hC, countablePiM_symmetric_rank_equality P C hC⟩

end Papers.Rockel2026XiFootrule
