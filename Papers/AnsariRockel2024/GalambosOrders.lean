import Papers.AnsariRockel2024.GalambosTails
import Papers.AnsariRockel2024.ExtremeValueOrders
import Mathlib.Analysis.MeanInequalitiesPow

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

private theorem galambos_kernel_inv_norm (δ x y : ℝ) (hx : 0<x) (hy : 0<y) :
    Verification.galambosTailKernel δ x y =
      (((x⁻¹)^δ+(y⁻¹)^δ)^(1/δ))⁻¹ := by
  unfold Verification.galambosTailKernel
  rw [Real.inv_rpow hx.le,Real.inv_rpow hy.le,← Real.rpow_neg hx.le,← Real.rpow_neg hy.le,
    ← Real.rpow_neg (add_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hy.le _)),neg_div]

private theorem galambos_kernel_mono (δ ε : ℝ) (hδ : 0<δ) (hδε : δ≤ε)
    (x y : ℝ) (hx : 0<x) (hy : 0<y) :
    Verification.galambosTailKernel δ x y ≤ Verification.galambosTailKernel ε x y := by
  rw [galambos_kernel_inv_norm δ x y hx hy,galambos_kernel_inv_norm ε x y hx hy]
  have hp : 0<((x⁻¹)^ε+(y⁻¹)^ε)^(1/ε) :=
    Real.rpow_pos_of_pos (add_pos (Real.rpow_pos_of_pos (inv_pos.mpr hx) _) (Real.rpow_pos_of_pos (inv_pos.mpr hy) _)) _
  simpa only [one_div] using one_div_le_one_div_of_le hp
    (Real.rpow_add_rpow_le (inv_nonneg.mpr hx.le) (inv_nonneg.mpr hy.le) hδ hδε)

theorem galambos_pickands_antitone (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) (hδε : δ≤ε)
    (t : I) (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    Verification.copulaPickands (Verification.galambos ε hε) t ≤
      Verification.copulaPickands (Verification.galambos δ hδ) t := by
  rw [galambos_pickands_interior ε hε t ht,galambos_pickands_interior δ hδ t ht]
  exact sub_le_sub_left (galambos_kernel_mono δ ε hδ hδε (t:ℝ) (1-(t:ℝ)) ht.1 (by linarith [ht.2])) 1

theorem galambos_lowerOrthant_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) (hδε : δ≤ε) :
    (Verification.galambos δ hδ).LowerOrthantLE (Verification.galambos ε hε) := by
  apply (extremeValue_pickands_order _ _ (galambos_isExtremeValue δ hδ) (galambos_isExtremeValue ε hε)).mpr
  intro t ht0 ht1
  exact galambos_pickands_antitone δ ε hδ hε hδε t ⟨ht0,ht1⟩

theorem galambos_schurBoth_mono (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) (hδε : δ≤ε) :
    (Verification.galambos δ hδ).SchurBothLE (Verification.galambos ε hε) := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (galambos_isExtremeValue δ hδ)
    (galambos_isExtremeValue ε hε) (galambos_isCI δ hδ) (galambos_isCI ε hε)).mpr
  intro t ht0 ht1
  exact galambos_pickands_antitone δ ε hδ hε hδε t ⟨ht0,ht1⟩

theorem galambos_lowerOrthant_iff (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    (Verification.galambos δ hδ).LowerOrthantLE (Verification.galambos ε hε) ↔ δ≤ε := by
  constructor
  · intro h
    have hh := h.upperTailDependence_le (galambos_tails δ hδ).2 (galambos_tails ε hε).2
    have he := (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ)<2)).mp hh
    have hm := (div_le_div_iff₀ hδ hε).mp he
    linarith
  · exact galambos_lowerOrthant_mono δ ε hδ hε

theorem galambos_schurBoth_iff (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    (Verification.galambos δ hδ).SchurBothLE (Verification.galambos ε hε) ↔ δ≤ε := by
  constructor
  · intro h
    apply (galambos_lowerOrthant_iff δ ε hδ hε).mp
    exact (cis_schur_iff_orthant _ _ (galambos_isCI δ hδ).1 (galambos_isCI ε hε).1).mp h.1
  · exact galambos_schurBoth_mono δ ε hδ hε

end Papers.AnsariRockel2024
