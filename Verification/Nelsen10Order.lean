import Verification.Nelsen10Dependence
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory
open Copula
open scoped unitInterval

namespace Verification

noncomputable def n10Half : I := ⟨1/2, by norm_num, by norm_num⟩
noncomputable def n10Low : I := ⟨1/16, by norm_num, by norm_num⟩
noncomputable def n10High : I := ⟨9/16, by norm_num, by norm_num⟩

theorem nelsen10_crossing_low :
    (nelsen10 n10Half).cdf ![n10Low,n10Low] < (nelsen10 1).cdf ![n10Low,n10Low] := by
  have hs := Real.rpow_rpow_inv (by norm_num : 0 ≤ (1/4:ℝ)) (by norm_num : (2:ℝ) ≠ 0)
  norm_num [Real.rpow_two] at hs
  rw [nelsen10_cdf _ _ _ (by norm_num [n10Half]), nelsen10_cdf _ _ _ (by norm_num)]
  norm_num [n10Half, n10Low, hs, Real.rpow_two]

theorem nelsen10_crossing_high :
    (nelsen10 1).cdf ![n10High,n10High] < (nelsen10 n10Half).cdf ![n10High,n10High] := by
  have hs := Real.rpow_rpow_inv (by norm_num : 0 ≤ (3/4:ℝ)) (by norm_num : (2:ℝ) ≠ 0)
  norm_num [Real.rpow_two] at hs
  rw [nelsen10_cdf _ _ _ (by norm_num), nelsen10_cdf _ _ _ (by norm_num [n10Half])]
  norm_num [n10Half, n10High, hs, Real.rpow_two]

theorem nelsen10_orthant_incomparable :
    ¬(nelsen10 n10Half).LowerOrthantLE (nelsen10 1) ∧
      ¬(nelsen10 1).LowerOrthantLE (nelsen10 n10Half) := by
  constructor
  · intro h
    exact (not_le_of_gt nelsen10_crossing_high) (h ![n10High,n10High])
  · intro h
    exact (not_le_of_gt nelsen10_crossing_low) (h ![n10Low,n10Low])

theorem nelsen10_schur_incomparable :
    ¬(nelsen10 n10Half).SchurLE (nelsen10 1) ∧
      ¬(nelsen10 1).SchurLE (nelsen10 n10Half) := by
  rw [schurLE_iff_lowerOrthantLE_isSD _ _ (nelsen10_isSD _) (nelsen10_isSD _),
    schurLE_iff_lowerOrthantLE_isSD _ _ (nelsen10_isSD _) (nelsen10_isSD _)]
  exact nelsen10_orthant_incomparable.symm

theorem nelsen10_schurBoth_incomparable :
    ¬(nelsen10 n10Half).SchurBothLE (nelsen10 1) ∧
      ¬(nelsen10 1).SchurBothLE (nelsen10 n10Half) :=
  ⟨fun h => nelsen10_schur_incomparable.1 h.1,
    fun h => nelsen10_schur_incomparable.2 h.1⟩

end Verification
