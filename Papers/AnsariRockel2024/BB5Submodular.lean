import Verification.ExtremeValuePowerLog
import Papers.AnsariRockel2024.GalambosDependence
import Verification.BB5Kernel

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem bb5_exponent_eq_power_log (θ δ x y : ℝ) (hδ : 0<δ) (hx : 0<x) (hy : 0<y) :
    Verification.bb5TailKernel θ δ x y=
      Verification.extremeValuePowerLog (Verification.galambos δ hδ) θ x y hx.le hy.le := by
  have hxp := Real.rpow_pos_of_pos hx θ
  have hyp := Real.rpow_pos_of_pos hy θ
  unfold Verification.extremeValuePowerLog Verification.extremeValueLog
  rw [galambos_cdf_interior δ hδ _ _
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hxp)⟩
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hyp)⟩]
  simp only [Verification.unitNegExp,Real.log_exp,neg_neg]
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp,Real.log_exp]
  unfold Verification.bb5TailKernel Verification.galambosTailKernel
  congr 1
  ring

theorem bb5_exponent_submodular (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : 0<x₁) (hy : 0<y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    Verification.bb5TailKernel θ δ x₁ y₁+Verification.bb5TailKernel θ δ x₂ y₂ ≤
      Verification.bb5TailKernel θ δ x₁ y₂+Verification.bb5TailKernel θ δ x₂ y₁ := by
  rw [bb5_exponent_eq_power_log θ δ x₁ y₁ hδ hx hy,
    bb5_exponent_eq_power_log θ δ x₂ y₂ hδ (hx.trans_le hxx) (hy.trans_le hyy),
    bb5_exponent_eq_power_log θ δ x₁ y₂ hδ hx (hy.trans_le hyy),
    bb5_exponent_eq_power_log θ δ x₂ y₁ hδ (hx.trans_le hxx) hy]
  exact Verification.extremeValuePowerLog_submodular _ (galambos_isExtremeValue δ hδ) θ hθ hx.le hy.le hxx hyy

end Papers.AnsariRockel2024
