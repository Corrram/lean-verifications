import Papers.Rockel2026XiFootrule.SIRegion
import Verification.OrdinalConditionalRank
import Copula.OrdinalSum.Rank

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- Rank equality is preserved by every binary ordinal sum, including endpoint splits. -/
theorem ordinalSum_xi_eq_footrule_of_components
    (C D : Copula 2) (a : I)
    (hC : C.chatterjeeXi = C.spearmanFootrule)
    (hD : D.chatterjeeXi = D.spearmanFootrule) :
    (C.ordinalSum D a).chatterjeeXi =
      (C.ordinalSum D a).spearmanFootrule := by
  rw [chatterjeeXi_ordinalSum, Copula.spearmanFootrule_ordinalSum, hC, hD]

/-- For SI components and an interior split, equality of the sum forces equality in each block. -/
theorem ordinalSum_xi_eq_footrule_iff
    (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1)
    (hC : C.IsSI) (hD : D.IsSI) :
    (C.ordinalSum D a).chatterjeeXi =
      (C.ordinalSum D a).spearmanFootrule ↔
      C.chatterjeeXi = C.spearmanFootrule ∧
        D.chatterjeeXi = D.spearmanFootrule := by
  constructor
  · intro h
    rw [chatterjeeXi_ordinalSum, Copula.spearmanFootrule_ordinalSum] at h
    have hc := si_xi_le_footrule C hC
    have hd := si_xi_le_footrule D hD
    have ha : 0 < (a : ℝ) := ha0
    have hb : 0 < 1 - (a : ℝ) := sub_pos.mpr ha1
    constructor <;> nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb]
  · rintro ⟨hc, hd⟩
    exact ordinalSum_xi_eq_footrule_of_components C D a hc hd

/-- Finite recursively nested ordinal sums of independence and comonotonic blocks. -/
inductive FinitePiOrdinal : Copula 2 → Prop
  | independence : FinitePiOrdinal (Copula.independence 2)
  | comonotonic : FinitePiOrdinal (Copula.comonotonic 2)
  | ordinalSum {C D : Copula 2} (hC : FinitePiOrdinal C)
      (hD : FinitePiOrdinal D) (a : I) : FinitePiOrdinal (C.ordinalSum D a)

/-- Every finite nested ordinal sum of Π and M blocks is symmetric and has ξ=ψ. -/
theorem FinitePiOrdinal.symmetric_rank_equality
    {C : Copula 2} (h : FinitePiOrdinal C) :
    C.IsExchangeable ∧ C.chatterjeeXi = C.spearmanFootrule := by
  induction h with
  | independence =>
      exact ⟨Copula.isExchangeable_independence, by simp⟩
  | comonotonic =>
      exact ⟨Copula.isExchangeable_comonotonic, by simp⟩
  | ordinalSum hC hD a ihC ihD =>
      exact ⟨ihC.1.ordinalSum ihD.1 a,
        ordinalSum_xi_eq_footrule_of_components _ _ a ihC.2 ihD.2⟩

end Papers.Rockel2026XiFootrule