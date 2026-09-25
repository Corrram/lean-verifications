import Papers.AnsariRockel2024.JoeExtremeValue

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

private theorem kernel_half (δ : ℝ) (hδ : 0<δ) (x y : ℝ) (hx : 0≤x) (hy : 0≤y) :
    ((x/2)^(-δ)+(y/2)^(-δ))^(-1/δ)=(1/2:ℝ)*(x^(-δ)+y^(-δ))^(-1/δ) := by
  rw [div_eq_mul_inv x,div_eq_mul_inv y,
    Real.mul_rpow hx (by norm_num : (0:ℝ)≤(2:ℝ)⁻¹),
    Real.mul_rpow hy (by norm_num : (0:ℝ)≤(2:ℝ)⁻¹),← add_mul,
    Real.mul_rpow (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)) (by positivity),
    ← Real.rpow_mul (by norm_num : (0:ℝ)≤(2:ℝ)⁻¹),
    show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one]
  ring

theorem joeExtremeValue_pickands_interior (δ : ℝ) (hδ : 0<δ) (α β t : I)
    (hα : 0<(α:ℝ)) (hβ : 0<(β:ℝ)) (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    Verification.copulaPickands (Verification.joeExtremeValue δ hδ α β) t =
      1-(((α:ℝ)*(1-(t:ℝ)))^(-δ)+((β:ℝ)*(t:ℝ))^(-δ))^(-1/δ) := by
  have hx : 0<(1-(t:ℝ))/2 := by linarith [ht.2]
  have hy : 0<(t:ℝ)/2 := by linarith [ht.1]
  unfold Verification.copulaPickands Verification.pickandsRay
  rw [joeExtremeValue_cdf_interior δ hδ α β _ _ hα hβ
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)⟩
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hy)⟩]
  simp only [Verification.unitNegExp,Real.log_exp,neg_neg]
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp,Real.log_exp,
    ← mul_div_assoc,← mul_div_assoc,
    kernel_half δ hδ _ _ (mul_nonneg α.property.1 (by linarith [ht.2]))
      (mul_nonneg β.property.1 ht.1.le)]
  ring

theorem joeExtremeValue_pickands_zero_weight (δ : ℝ) (hδ : 0<δ) (α β t : I)
    (h : α=0 ∨ β=0) :
    Verification.copulaPickands (Verification.joeExtremeValue δ hδ α β) t=1 := by
  rw [joeExtremeValue_zero_weight δ hδ α β h]
  unfold Verification.copulaPickands Verification.pickandsRay
  rw [cdf_independence]
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Verification.unitNegExp]
  rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp]
  ring

theorem joeExtremeValue_pickands_endpoints (δ : ℝ) (hδ : 0<δ) (α β : I) :
    Verification.copulaPickands (Verification.joeExtremeValue δ hδ α β) 0=1 ∧
    Verification.copulaPickands (Verification.joeExtremeValue δ hδ α β) 1=1 :=
  ⟨Verification.copulaPickands_zero _,Verification.copulaPickands_one _⟩

end Papers.AnsariRockel2024
