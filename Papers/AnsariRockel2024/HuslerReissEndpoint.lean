import Papers.AnsariRockel2024.HuslerReissOrders
import Copula.TailDependence.Examples

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

noncomputable def huslerReiss (δ : ℝ) (hδ : 0≤δ) : Copula 2 :=
  if h : δ=0 then independence 2 else huslerReissPositive δ (lt_of_le_of_ne hδ (Ne.symm h))

end Verification

namespace Papers.AnsariRockel2024

theorem huslerReiss_zero : Verification.huslerReiss 0 le_rfl=independence 2 := by
  simp [Verification.huslerReiss]

theorem huslerReiss_positive (δ : ℝ) (hδ : 0<δ) :
    Verification.huslerReiss δ hδ.le=Verification.huslerReissPositive δ hδ := by
  simp [Verification.huslerReiss,hδ.ne']

theorem huslerReiss_closed_isExtremeValue (δ : ℝ) (hδ : 0≤δ) :
    (Verification.huslerReiss δ hδ).IsExtremeValue := by
  rcases hδ.eq_or_lt with h|h
  · subst δ; rw [huslerReiss_zero]; exact isExtremeValue_independence 2
  · rw [huslerReiss_positive δ h]; exact Verification.huslerReissPositive_isExtremeValue δ h

theorem huslerReiss_closed_isCI (δ : ℝ) (hδ : 0≤δ) :
    (Verification.huslerReiss δ hδ).IsCI :=
  Verification.extremeValue_isCI _ (huslerReiss_closed_isExtremeValue δ hδ)

theorem huslerReiss_closed_tails (δ : ℝ) (hδ : 0≤δ) :
    (Verification.huslerReiss δ hδ).HasLowerTailDependence 0 ∧
    (Verification.huslerReiss δ hδ).HasUpperTailDependence
      (if δ=0 then 0 else 2-2*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ)) := by
  rcases hδ.eq_or_lt with h|h
  · subst δ; rw [huslerReiss_zero]; simp only [ite_true]
    exact ⟨hasLowerTailDependence_independence,hasUpperTailDependence_independence⟩
  · rw [huslerReiss_positive δ h,ite_eq_right h.ne']
    exact huslerReiss_tails δ h

theorem huslerReiss_closed_lowerOrthant_mono (δ ε : ℝ) (hδ : 0≤δ) (hε : 0≤ε) (hδε : δ≤ε) :
    (Verification.huslerReiss δ hδ).LowerOrthantLE (Verification.huslerReiss ε hε) := by
  rcases hδ.eq_or_lt with h|h
  · subst δ
    rw [huslerReiss_zero]
    exact (isPQD_iff_independence_le _).mp (huslerReiss_closed_isCI ε hε).isPQD
  · have he := h.trans_le hδε
    rw [huslerReiss_positive δ h,huslerReiss_positive ε he]
    exact huslerReiss_lowerOrthant_mono δ ε h he hδε

theorem huslerReiss_closed_schurBoth_mono (δ ε : ℝ) (hδ : 0≤δ) (hε : 0≤ε) (hδε : δ≤ε) :
    (Verification.huslerReiss δ hδ).SchurBothLE (Verification.huslerReiss ε hε) := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (huslerReiss_closed_isExtremeValue δ hδ)
    (huslerReiss_closed_isExtremeValue ε hε) (huslerReiss_closed_isCI δ hδ)
    (huslerReiss_closed_isCI ε hε)).mpr
  exact (extremeValue_pickands_order _ _ (huslerReiss_closed_isExtremeValue δ hδ)
    (huslerReiss_closed_isExtremeValue ε hε)).mp (huslerReiss_closed_lowerOrthant_mono δ ε hδ hε hδε)

theorem huslerReiss_closed_lowerOrthant_iff (δ ε : ℝ) (hδ : 0≤δ) (hε : 0≤ε) :
    (Verification.huslerReiss δ hδ).LowerOrthantLE (Verification.huslerReiss ε hε) ↔ δ≤ε := by
  constructor
  · intro h
    rcases hδ.eq_or_lt with hd|hd
    · subst δ; exact hε
    rcases hε.eq_or_lt with he|he
    · subst ε
      rw [huslerReiss_zero,huslerReiss_positive δ hd] at h
      have ht := h.upperTailDependence_le (huslerReiss_tails δ hd).2 hasUpperTailDependence_independence
      have hn := Verification.standardNormalCDF_strictMono (show 1/δ<1/δ+1 by linarith)
      have hb := ProbabilityTheory.cdf_le_one (gaussianReal 0 1) (1/δ+1)
      linarith
    · rw [huslerReiss_positive δ hd,huslerReiss_positive ε he] at h
      exact (huslerReiss_lowerOrthant_iff δ ε hd he).mp h
  · exact huslerReiss_closed_lowerOrthant_mono δ ε hδ hε

theorem huslerReiss_closed_schurBoth_iff (δ ε : ℝ) (hδ : 0≤δ) (hε : 0≤ε) :
    (Verification.huslerReiss δ hδ).SchurBothLE (Verification.huslerReiss ε hε) ↔ δ≤ε := by
  constructor
  · intro h
    apply (huslerReiss_closed_lowerOrthant_iff δ ε hδ hε).mp
    exact (cis_schur_iff_orthant _ _ (huslerReiss_closed_isCI δ hδ).1
      (huslerReiss_closed_isCI ε hε).1).mp h.1
  · exact huslerReiss_closed_schurBoth_mono δ ε hδ hε

end Papers.AnsariRockel2024
