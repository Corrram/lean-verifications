import Verification.ExtremeValuePowerLog

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem exp_neg_four_point {a b c d : ℝ} (hab : a≤b) (hac : a≤c) (hs : a+d≤b+c) :
    0≤Real.exp (-a)-Real.exp (-b)-Real.exp (-c)+Real.exp (-d) := by
  have h1 := Real.exp_le_exp.mpr (neg_le_neg hab)
  have h2 := Real.exp_le_exp.mpr (neg_le_neg hac)
  have hp : Real.exp (-b)*Real.exp (-c)≤Real.exp (-a)*Real.exp (-d) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hmul := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)
  nlinarith [Real.exp_pos (-a)]

theorem extremeValuePowerLog_mono (C : Copula 2) (hC : C.IsExtremeValue)
    (θ : ℝ) (hθ : 1≤θ) {x₁ x₂ y₁ y₂ : ℝ}
    (hx : 0≤x₁) (hy : 0≤y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    extremeValuePowerLog C θ x₁ y₁ hx hy ≤
      extremeValuePowerLog C θ x₂ y₂ (hx.trans hxx) (hy.trans hyy) := by
  have ht : 0<θ := by linarith
  have hxp := Real.rpow_le_rpow hx hxx ht.le
  have hyp := Real.rpow_le_rpow hy hyy ht.le
  have hx0 := Real.rpow_nonneg hx θ
  have hy0 := Real.rpow_nonneg hy θ
  have hx2 := Real.rpow_nonneg (hx.trans hxx) θ
  unfold extremeValuePowerLog
  apply Real.rpow_le_rpow _ _ (one_div_nonneg.mpr ht.le)
  · exact (hx0.trans (le_max_left _ _)).trans (extremeValueLog_bounds C hC _ _ hx0 hy0).1
  · have h1 := (extremeValueLog_increment_first C hC hx0 hy0 hxp).1
    have h2 := (extremeValueLog_increment_second C hC hx2 hy0 hyp).1
    linarith

theorem extremeValuePowerLog_exp_rectangle (C : Copula 2) (hC : C.IsExtremeValue)
    (θ : ℝ) (hθ : 1≤θ) {x₁ x₂ y₁ y₂ : ℝ}
    (hx : 0≤x₁) (hy : 0≤y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    0≤Real.exp (-extremeValuePowerLog C θ x₁ y₁ hx hy)-
      Real.exp (-extremeValuePowerLog C θ x₁ y₂ hx (hy.trans hyy))-
      Real.exp (-extremeValuePowerLog C θ x₂ y₁ (hx.trans hxx) hy)+
      Real.exp (-extremeValuePowerLog C θ x₂ y₂ (hx.trans hxx) (hy.trans hyy)) := by
  exact exp_neg_four_point
    (extremeValuePowerLog_mono C hC θ hθ hx hy le_rfl hyy)
    (extremeValuePowerLog_mono C hC θ hθ hx hy hxx le_rfl)
    (extremeValuePowerLog_submodular C hC θ hθ hx hy hxx hyy)

end Verification
