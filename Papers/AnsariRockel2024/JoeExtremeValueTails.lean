import Papers.AnsariRockel2024.JoeExtremeValuePickands
import Verification.PickandsDiagonal
import Copula.TailDependence.Examples

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem joeExtremeValue_extremalCoefficient (δ : ℝ) (hδ : 0<δ) (α β : I)
    (hα : 0<(α:ℝ)) (hβ : 0<(β:ℝ)) :
    (Verification.joeExtremeValue δ hδ α β).extremalCoefficient=
      2-((α:ℝ)^(-δ)+(β:ℝ)^(-δ))^(-1/δ) := by
  rw [Verification.extremalCoefficient_eq_twice_pickands _ (joeExtremeValue_isExtremeValue δ hδ α β),
    joeExtremeValue_pickands_interior δ hδ α β unitHalf hα hβ (by norm_num [unitHalf])]
  norm_num only [unitHalf,show (1:ℝ)-1/2=1/2 by norm_num]
  rw [Real.mul_rpow α.property.1 (by norm_num : (0:ℝ)≤1/2),
    Real.mul_rpow β.property.1 (by norm_num : (0:ℝ)≤1/2),← add_mul,
    Real.mul_rpow (add_nonneg (Real.rpow_nonneg α.property.1 _) (Real.rpow_nonneg β.property.1 _)) (by positivity),
    ← Real.rpow_mul (by norm_num : (0:ℝ)≤1/2),show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one]
  ring

private theorem joeExtremeValue_exponent_gt_one (δ : ℝ) (hδ : 0<δ) (α β : I)
    (hα : 0<(α:ℝ)) (hβ : 0<(β:ℝ)) :
    1<2-((α:ℝ)^(-δ)+(β:ℝ)^(-δ))^(-1/δ) := by
  have ha := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hα α.property.2 (neg_nonpos.mpr hδ.le)
  have hb := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hβ β.property.2 (neg_nonpos.mpr hδ.le)
  have hc := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<2)
    (show (2:ℝ)≤(α:ℝ)^(-δ)+(β:ℝ)^(-δ) by linarith)
    (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1:ℝ)≤0) hδ.le)
  have hd := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2)
    (div_neg_of_neg_of_pos (by norm_num : (-1:ℝ)<0) hδ)
  rw [Real.rpow_zero] at hd
  linarith

theorem joeExtremeValue_tails (δ : ℝ) (hδ : 0<δ) (α β : I) :
    (Verification.joeExtremeValue δ hδ α β).HasLowerTailDependence 0 ∧
    (Verification.joeExtremeValue δ hδ α β).HasUpperTailDependence
      (if α=0 ∨ β=0 then 0 else ((α:ℝ)^(-δ)+(β:ℝ)^(-δ))^(-1/δ)) := by
  by_cases hz : α=0 ∨ β=0
  · rw [joeExtremeValue_zero_weight δ hδ α β hz,ite_eq_left hz]
    exact ⟨hasLowerTailDependence_independence,hasUpperTailDependence_independence⟩
  rw [ite_eq_right hz]
  have hα : 0<(α:ℝ) := lt_of_le_of_ne α.property.1 (fun h => hz (Or.inl (Subtype.ext h.symm)))
  have hβ : 0<(β:ℝ) := lt_of_le_of_ne β.property.1 (fun h => hz (Or.inr (Subtype.ext h.symm)))
  have he := joeExtremeValue_extremalCoefficient δ hδ α β hα hβ
  have hp := (joeExtremeValue_isExtremeValue δ hδ α β).hasPowerDiagonal
  rw [he] at hp
  exact ⟨hp.hasLowerTailDependence_zero (joeExtremeValue_exponent_gt_one δ hδ α β hα hβ),
    by simpa only [sub_sub_cancel] using hp.hasUpperTailDependence⟩

end Papers.AnsariRockel2024
