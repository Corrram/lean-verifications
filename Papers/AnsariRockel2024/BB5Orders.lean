import Papers.AnsariRockel2024.BB5Tails
import Papers.AnsariRockel2024.GalambosOrders

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem bb5_pickands_antitone (θ δ ε : ℝ) (hθ : 1≤θ) (hδ : 0<δ) (hε : 0<ε)
    (hδε : δ≤ε) (t : I) (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    Verification.copulaPickands (Verification.bb5 θ ε hθ hε) t ≤
      Verification.copulaPickands (Verification.bb5 θ δ hθ hδ) t := by
  have hx : 0<1-(t:ℝ) := by linarith [ht.2]
  rw [bb5_pickands_interior θ ε hθ hε t ht,bb5_pickands_interior θ δ hθ hδ t ht,
    bb5_exponent_eq_power_log θ ε _ _ hε hx ht.1,
    bb5_exponent_eq_power_log θ δ _ _ hδ hx ht.1]
  unfold Verification.extremeValuePowerLog
  apply Real.rpow_le_rpow
  · have h := (Verification.extremeValueLog_bounds (Verification.galambos ε hε)
      (galambos_isExtremeValue ε hε) ((1-(t:ℝ))^θ) ((t:ℝ)^θ)
      (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg ht.1.le _)).1
    exact (Real.rpow_nonneg hx.le θ).trans ((le_max_left _ _).trans h)
  · unfold Verification.extremeValueLog
    exact neg_le_neg (Real.log_le_log
      (Verification.extremeValue_exp_cdf_pos _ (galambos_isExtremeValue δ hδ) _ _ _ _)
      (galambos_lowerOrthant_mono δ ε hδ hε hδε _))
  · positivity

theorem bb5_lowerOrthant_mono (θ δ ε : ℝ) (hθ : 1≤θ) (hδ : 0<δ) (hε : 0<ε)
    (hδε : δ≤ε) :
    (Verification.bb5 θ δ hθ hδ).LowerOrthantLE (Verification.bb5 θ ε hθ hε) := by
  apply (extremeValue_pickands_order _ _ (bb5_isExtremeValue θ δ hθ hδ)
    (bb5_isExtremeValue θ ε hθ hε)).mpr
  intro t ht0 ht1
  exact bb5_pickands_antitone θ δ ε hθ hδ hε hδε t ⟨ht0,ht1⟩

theorem bb5_schurBoth_mono (θ δ ε : ℝ) (hθ : 1≤θ) (hδ : 0<δ) (hε : 0<ε)
    (hδε : δ≤ε) :
    (Verification.bb5 θ δ hθ hδ).SchurBothLE (Verification.bb5 θ ε hθ hε) := by
  apply (extremeValue_schur_iff_pickands_of_ci _ _ (bb5_isExtremeValue θ δ hθ hδ)
    (bb5_isExtremeValue θ ε hθ hε) (bb5_isCI θ δ hθ hδ) (bb5_isCI θ ε hθ hε)).mpr
  intro t ht0 ht1
  exact bb5_pickands_antitone θ δ ε hθ hδ hε hδε t ⟨ht0,ht1⟩

end Papers.AnsariRockel2024
