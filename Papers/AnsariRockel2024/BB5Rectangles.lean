import Papers.AnsariRockel2024.BB5Submodular
import Verification.ExtremeValuePowerRectangle

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

noncomputable def bb5InteriorCDF (θ δ u v : ℝ) : ℝ :=
  Real.exp (-bb5TailKernel θ δ (-Real.log u) (-Real.log v))

end Verification

namespace Papers.AnsariRockel2024

theorem bb5_exponent_exp_rectangle (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : 0<x₁) (hy : 0<y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    0≤Real.exp (-Verification.bb5TailKernel θ δ x₁ y₁)-
      Real.exp (-Verification.bb5TailKernel θ δ x₁ y₂)-
      Real.exp (-Verification.bb5TailKernel θ δ x₂ y₁)+
      Real.exp (-Verification.bb5TailKernel θ δ x₂ y₂) := by
  rw [bb5_exponent_eq_power_log θ δ x₁ y₁ hδ hx hy,
    bb5_exponent_eq_power_log θ δ x₂ y₂ hδ (hx.trans_le hxx) (hy.trans_le hyy),
    bb5_exponent_eq_power_log θ δ x₁ y₂ hδ hx (hy.trans_le hyy),
    bb5_exponent_eq_power_log θ δ x₂ y₁ hδ (hx.trans_le hxx) hy]
  exact Verification.extremeValuePowerLog_exp_rectangle _ (galambos_isExtremeValue δ hδ) θ hθ hx.le hy.le hxx hyy

theorem bb5_interior_rectangle_nonneg (θ δ : ℝ) (hθ : 1≤θ) (hδ : 0<δ)
    {a b c d : ℝ} (ha : 0<a) (hab : a≤b) (hb : b<1)
    (hc : 0<c) (hcd : c≤d) (hd : d<1) :
    0≤Verification.bb5InteriorCDF θ δ b d-Verification.bb5InteriorCDF θ δ a d-
      Verification.bb5InteriorCDF θ δ b c+Verification.bb5InteriorCDF θ δ a c := by
  have h := bb5_exponent_exp_rectangle θ δ hθ hδ
    (neg_pos.mpr (Real.log_neg (ha.trans_le hab) hb))
    (neg_pos.mpr (Real.log_neg (hc.trans_le hcd) hd))
    (neg_le_neg (Real.log_le_log ha hab)) (neg_le_neg (Real.log_le_log hc hcd))
  unfold Verification.bb5InteriorCDF
  linarith

end Papers.AnsariRockel2024
