import Papers.AnsariRockel2024.GalambosDependence

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Verification

noncomputable def joeExtremeValue (δ : ℝ) (hδ : 0<δ) (α β : I) : Copula 2 :=
  maxProduct (galambos δ hδ) (independence 2) ![α,β]

end Verification

namespace Papers.AnsariRockel2024

theorem joeExtremeValue_isExtremeValue (δ : ℝ) (hδ : 0<δ) (α β : I) :
    (Verification.joeExtremeValue δ hδ α β).IsExtremeValue :=
  (galambos_isExtremeValue δ hδ).maxProduct (isExtremeValue_independence 2) _

theorem joeExtremeValue_isCI (δ : ℝ) (hδ : 0<δ) (α β : I) :
    (Verification.joeExtremeValue δ hδ α β).IsCI :=
  Verification.extremeValue_isCI _ (joeExtremeValue_isExtremeValue δ hδ α β)

theorem joeExtremeValue_cdf_product (δ : ℝ) (hδ : 0<δ) (α β u v : I) :
    (Verification.joeExtremeValue δ hδ α β).cdf ![u,v] =
      (Verification.galambos δ hδ).cdf ![unitPower u α α.property.1,unitPower v β β.property.1]*
        ((u:ℝ)^(1-(α:ℝ))*(v:ℝ)^(1-(β:ℝ))) := by
  rw [Verification.joeExtremeValue,cdf_maxProduct,cdf_independence]
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,coe_unitPower,
    unitInterval.coe_symm_eq]
  congr 2
  ext i
  fin_cases i <;> rfl

theorem joeExtremeValue_cdf_interior (δ : ℝ) (hδ : 0<δ) (α β u v : I)
    (hα : 0<(α:ℝ)) (hβ : 0<(β:ℝ))
    (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (Verification.joeExtremeValue δ hδ α β).cdf ![u,v] =
      (u:ℝ)*(v:ℝ)*Real.exp
        ((((α:ℝ)*(-Real.log (u:ℝ)))^(-δ)+((β:ℝ)*(-Real.log (v:ℝ)))^(-δ))^(-1/δ)) := by
  rw [joeExtremeValue_cdf_product,galambos_cdf_interior δ hδ _ _
    ⟨Real.rpow_pos_of_pos hu.1 _,Real.rpow_lt_one u.property.1 hu.2 hα⟩
    ⟨Real.rpow_pos_of_pos hv.1 _,Real.rpow_lt_one v.property.1 hv.2 hβ⟩]
  simp only [coe_unitPower,Real.log_rpow hu.1,Real.log_rpow hv.1,neg_mul_eq_mul_neg]
  have hu' : (u:ℝ)^(α:ℝ)*(u:ℝ)^(1-(α:ℝ))=(u:ℝ) := by
    rw [← Real.rpow_add hu.1,add_sub_cancel,Real.rpow_one]
  have hv' : (v:ℝ)^(β:ℝ)*(v:ℝ)^(1-(β:ℝ))=(v:ℝ) := by
    rw [← Real.rpow_add hv.1,add_sub_cancel,Real.rpow_one]
  calc
    _ = ((u:ℝ)^(α:ℝ)*(u:ℝ)^(1-(α:ℝ)))*((v:ℝ)^(β:ℝ)*(v:ℝ)^(1-(β:ℝ)))*
      Real.exp (((((α:ℝ)*(-Real.log (u:ℝ)))^(-δ)+((β:ℝ)*(-Real.log (v:ℝ)))^(-δ))^(-1/δ))) := by ring
    _ = _ := by rw [hu',hv']

theorem joeExtremeValue_unit_weights (δ : ℝ) (hδ : 0<δ) :
    Verification.joeExtremeValue δ hδ 1 1=Verification.galambos δ hδ := by
  unfold Verification.joeExtremeValue
  have he : (![(1:I),1]:Fin 2→I)=fun _ => 1 := by ext i; fin_cases i <;> rfl
  rw [he,maxProduct_one]

theorem joeExtremeValue_zero_weight (δ : ℝ) (hδ : 0<δ) (α β : I)
    (h : α=0 ∨ β=0) : Verification.joeExtremeValue δ hδ α β=independence 2 := by
  apply ext_cdf
  intro u
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  by_cases hz : ∃ j,u j=0
  · obtain ⟨j,hj⟩ := hz
    rw [cdf_eq_zero_of_coord_eq_zero _ _ j hj,cdf_eq_zero_of_coord_eq_zero _ _ j hj]
  have hp (j) : 0<(u j:ℝ) := lt_of_le_of_ne (u j).property.1
    (fun hh => hz ⟨j,Subtype.ext hh.symm⟩)
  conv_lhs => rw [hu,joeExtremeValue_cdf_product]
  rw [cdf_independence]
  simp only [Fin.prod_univ_two]
  have he (j : Fin 2) (a : I) : (u j:ℝ)^(a:ℝ)*(u j:ℝ)^(1-(a:ℝ))=(u j:ℝ) := by
    rw [← Real.rpow_add (hp j),add_sub_cancel,Real.rpow_one]
  rcases h with rfl|rfl
  · simp only [unitPower_zero,cdf_two_one_left,coe_unitPower,Set.Icc.coe_zero,sub_zero,Real.rpow_one]
    calc
      _ = (u 0:ℝ)*((u 1:ℝ)^(β:ℝ)*(u 1:ℝ)^(1-(β:ℝ))) := by ring
      _ = _ := by rw [he]
  · simp only [unitPower_zero,cdf_two_one_right,coe_unitPower,Set.Icc.coe_zero,sub_zero,Real.rpow_one]
    rw [← mul_assoc,he]

end Papers.AnsariRockel2024
