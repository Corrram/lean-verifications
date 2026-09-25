import Verification.ConcaveFourPoint
import Verification.ExtremeValueLog
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

open ProbabilityTheory Real Set Copula
open scoped unitInterval

namespace Verification

noncomputable def extremeValuePowerLog (C : Copula 2) (θ x y : ℝ) (hx : 0≤x) (hy : 0≤y) : ℝ :=
  (extremeValueLog C (x^θ) (y^θ) (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _))^(1/θ)

theorem extremeValuePowerLog_submodular (C : Copula 2) (hC : C.IsExtremeValue)
    (θ : ℝ) (hθ : 1≤θ) {x₁ x₂ y₁ y₂ : ℝ}
    (hx : 0≤x₁) (hy : 0≤y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    extremeValuePowerLog C θ x₁ y₁ hx hy +
      extremeValuePowerLog C θ x₂ y₂ (hx.trans hxx) (hy.trans hyy) ≤
    extremeValuePowerLog C θ x₁ y₂ hx (hy.trans hyy) +
      extremeValuePowerLog C θ x₂ y₁ (hx.trans hxx) hy := by
  have ht : 0<θ := by linarith
  have hxp := Real.rpow_le_rpow hx hxx ht.le
  have hyp := Real.rpow_le_rpow hy hyy ht.le
  have hx0 := Real.rpow_nonneg hx θ
  have hy0 := Real.rpow_nonneg hy θ
  have hx2 := Real.rpow_nonneg (hx.trans hxx) θ
  have hy2 := Real.rpow_nonneg (hy.trans hyy) θ
  unfold extremeValuePowerLog
  apply concave_monotone_four_point
    (Real.concaveOn_rpow (one_div_nonneg.mpr ht.le) ((div_le_one ht).mpr hθ))
    (fun a ha b _ hab => Real.rpow_le_rpow ha hab (one_div_nonneg.mpr ht.le))
  · exact (le_max_left _ _).trans' hx0 |>.trans (extremeValueLog_bounds C hC _ _ hx0 hy0).1
  · exact sub_nonneg.mp (extremeValueLog_increment_second C hC hx0 hy0 hyp).1
  · exact sub_nonneg.mp (extremeValueLog_increment_first C hC hx0 hy2 hxp).1
  · exact sub_nonneg.mp (extremeValueLog_increment_first C hC hx0 hy0 hxp).1
  · exact extremeValueLog_submodular C hC hx0 hy0 hxp hyp

end Verification
