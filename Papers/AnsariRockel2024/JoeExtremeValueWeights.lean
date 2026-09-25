import Papers.AnsariRockel2024.JoeExtremeValueOrders
import Papers.AnsariRockel2024.JoeExtremeValuePickands

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem joeExtremeValue_weight_lowerOrthant_mono (δ : ℝ) (hδ : 0<δ)
    (α β α' β' : I) (hα : α≤α') (hβ : β≤β') :
    (Verification.joeExtremeValue δ hδ α β).LowerOrthantLE
      (Verification.joeExtremeValue δ hδ α' β') := by
  by_cases hz : α=0 ∨ β=0
  · rw [joeExtremeValue_zero_weight δ hδ α β hz]
    exact (isPQD_iff_independence_le _).mp (joeExtremeValue_isCI δ hδ α' β').isPQD
  have ha : 0<(α:ℝ) := lt_of_le_of_ne α.property.1 (fun h => hz (Or.inl (Subtype.ext h.symm)))
  have hb : 0<(β:ℝ) := lt_of_le_of_ne β.property.1 (fun h => hz (Or.inr (Subtype.ext h.symm)))
  have ha' : 0<(α':ℝ) := lt_of_lt_of_le ha hα
  have hb' : 0<(β':ℝ) := lt_of_lt_of_le hb hβ
  apply (extremeValue_pickands_order _ _ (joeExtremeValue_isExtremeValue δ hδ α β)
    (joeExtremeValue_isExtremeValue δ hδ α' β')).mpr
  intro t ht0 ht1
  have ht : (t:ℝ)∈Ioo (0:ℝ) 1 := ⟨ht0,ht1⟩
  rw [joeExtremeValue_pickands_interior δ hδ α β t ha hb ht,
    joeExtremeValue_pickands_interior δ hδ α' β' t ha' hb' ht]
  apply sub_le_sub_left
  have ht' : 0<1-(t:ℝ) := by linarith [ht.2]
  have h1 := Real.rpow_le_rpow_of_nonpos (mul_pos ha ht')
    (mul_le_mul_of_nonneg_right hα ht'.le) (neg_nonpos.mpr hδ.le)
  have h2 := Real.rpow_le_rpow_of_nonpos (mul_pos hb ht.1)
    (mul_le_mul_of_nonneg_right hβ ht.1.le) (neg_nonpos.mpr hδ.le)
  exact Real.rpow_le_rpow_of_nonpos
    (add_pos (Real.rpow_pos_of_pos (mul_pos ha' ht') _) (Real.rpow_pos_of_pos (mul_pos hb' ht.1) _))
    (add_le_add h1 h2) (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1:ℝ)≤0) hδ.le)

theorem joeExtremeValue_weight_schurBoth_mono (δ : ℝ) (hδ : 0<δ)
    (α β α' β' : I) (hα : α≤α') (hβ : β≤β') :
    (Verification.joeExtremeValue δ hδ α β).SchurBothLE
      (Verification.joeExtremeValue δ hδ α' β') := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (joeExtremeValue_isExtremeValue δ hδ α β)
    (joeExtremeValue_isExtremeValue δ hδ α' β') (joeExtremeValue_isCI δ hδ α β)
    (joeExtremeValue_isCI δ hδ α' β')).mpr
  exact (extremeValue_pickands_order _ _ (joeExtremeValue_isExtremeValue δ hδ α β)
    (joeExtremeValue_isExtremeValue δ hδ α' β')).mp
    (joeExtremeValue_weight_lowerOrthant_mono δ hδ α β α' β' hα hβ)

theorem joeExtremeValue_allParameters_lowerOrthant_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε)
    (hδε : δ≤ε) (α β α' β' : I) (hα : α≤α') (hβ : β≤β') :
    (Verification.joeExtremeValue δ hδ α β).LowerOrthantLE
      (Verification.joeExtremeValue ε hε α' β') := by
  intro u
  exact (joeExtremeValue_lowerOrthant_mono δ ε hδ hε hδε α β u).trans
    (joeExtremeValue_weight_lowerOrthant_mono ε hε α β α' β' hα hβ u)

theorem joeExtremeValue_allParameters_schurBoth_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε)
    (hδε : δ≤ε) (α β α' β' : I) (hα : α≤α') (hβ : β≤β') :
    (Verification.joeExtremeValue δ hδ α β).SchurBothLE
      (Verification.joeExtremeValue ε hε α' β') := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (joeExtremeValue_isExtremeValue δ hδ α β)
    (joeExtremeValue_isExtremeValue ε hε α' β') (joeExtremeValue_isCI δ hδ α β)
    (joeExtremeValue_isCI ε hε α' β')).mpr
  exact (extremeValue_pickands_order _ _ (joeExtremeValue_isExtremeValue δ hδ α β)
    (joeExtremeValue_isExtremeValue ε hε α' β')).mp
    (joeExtremeValue_allParameters_lowerOrthant_mono δ ε hδ hε hδε α β α' β' hα hβ)

end Papers.AnsariRockel2024
