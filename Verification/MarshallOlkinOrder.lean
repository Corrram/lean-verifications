import Verification.SchurOrthantEquivalence
import Copula.Families.MarshallOlkin
import Copula.Order.SymmetricSchur
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! # Conditional increase and order of Marshall–Olkin copulas -/

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem isSI_of_concave_formula (C : Copula 2) (f : I → ℝ → ℝ)
    (hf : ∀ v, ConcaveOn ℝ (Icc 0 1) (f v))
    (he : ∀ u v : I, C.cdf ![u,v]=f v u) : C.IsSI := by
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with rfl | hab
  · simp
  rcases eq_or_lt_of_le hbc with rfl | hbc
  · simp
  have hh := (hf v).slope_anti_adjacent a.property c.property hab hbc
  have hh' := (div_le_div_iff₀ (sub_pos.mpr (show (b:ℝ)<c from hbc)) (sub_pos.mpr (show (a:ℝ)<b from hab))).mp hh
  simp_rw [he]
  nlinarith only [hh']

/-- The paper's minimum formula, including all boundary and parameter endpoints. -/
theorem marshallOlkin_cdf_min (α β u v : I) :
    (marshallOlkin α β).cdf ![u,v] =
      min ((u:ℝ)^(1-(α:ℝ))*(v:ℝ)) ((u:ℝ)*(v:ℝ)^(1-(β:ℝ))) := by
  by_cases hu : u=0
  · subst u
    simp only [cdf_two_zero_left,Set.Icc.coe_zero,zero_mul]
    exact (min_eq_right (mul_nonneg (Real.rpow_nonneg (by norm_num) _) v.property.1)).symm
  by_cases hv : v=0
  · subst v
    simp only [cdf_two_zero_right,Set.Icc.coe_zero,mul_zero]
    exact (min_eq_left (mul_nonneg u.property.1 (Real.rpow_nonneg (by norm_num) _))).symm
  have hup : (0:ℝ)<u := lt_of_le_of_ne u.property.1 (Ne.symm (fun he => hu (Subtype.ext he)))
  have hvp : (0:ℝ)<v := lt_of_le_of_ne v.property.1 (Ne.symm (fun he => hv (Subtype.ext he)))
  rw [cdf_marshallOlkin]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [min_mul_of_nonneg _ _ (mul_nonneg (Real.rpow_nonneg u.property.1 _) (Real.rpow_nonneg v.property.1 _))]
  have h₁ : (u:ℝ)^(α:ℝ)*((u:ℝ)^(1-(α:ℝ))*(v:ℝ)^(1-(β:ℝ))) = (u:ℝ)*(v:ℝ)^(1-(β:ℝ)) := by
    rw [← mul_assoc,← Real.rpow_add hup]
    simp
  have h₂ : (v:ℝ)^(β:ℝ)*((u:ℝ)^(1-(α:ℝ))*(v:ℝ)^(1-(β:ℝ))) = (u:ℝ)^(1-(α:ℝ))*(v:ℝ) := by
    rw [mul_left_comm,← Real.rpow_add hvp]
    simp
  rw [h₁,h₂,min_comm]

theorem marshallOlkin_transpose (α β : I) : (marshallOlkin α β).transpose=marshallOlkin β α := by
  apply Copula.ext_cdf
  intro x
  have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx,Copula.cdf_transpose,marshallOlkin_cdf_min,marshallOlkin_cdf_min]
  simp only [mul_comm,min_comm]

theorem marshallOlkin_isSI (α β : I) : (marshallOlkin α β).IsSI := by
  apply isSI_of_concave_formula _
    (fun v u => min (u^(1-(α:ℝ))*(v:ℝ)) (u*(v:ℝ)^(1-(β:ℝ)))) _
    (marshallOlkin_cdf_min α β)
  intro v
  have hp : ConcaveOn ℝ (Icc 0 1) (fun u : ℝ => u^(1-(α:ℝ))) :=
    (Real.concaveOn_rpow (by linarith [α.property.2]) (by linarith [α.property.1])).subset
      (fun _ h => h.1) (convex_Icc _ _)
  have h₁ := ConcaveOn.smul v.property.1 hp
  have h₂ := ConcaveOn.smul (Real.rpow_nonneg v.property.1 (1-(β:ℝ)))
    (concaveOn_id (convex_Icc (0:ℝ) 1))
  have hh := h₁.inf h₂
  change ConcaveOn ℝ (Icc 0 1)
    (fun u : ℝ => min ((v:ℝ)*u^(1-(α:ℝ))) ((v:ℝ)^(1-(β:ℝ))*u)) at hh
  simpa only [mul_comm] using hh

theorem marshallOlkin_isCI (α β : I) : (marshallOlkin α β).IsCI :=
  ⟨marshallOlkin_isSI α β,by rw [marshallOlkin_transpose]; exact marshallOlkin_isSI β α⟩

theorem marshallOlkin_lowerOrthant_mono {α β α' β' : I} (ha : α≤α') (hb : β≤β') :
    (marshallOlkin α β).LowerOrthantLE (marshallOlkin α' β') := by
  intro x
  have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  by_cases hu : x 0=0
  · simp [hu]
  by_cases hv : x 1=0
  · simp [hv]
  have hup : (0:ℝ)<x 0 := lt_of_le_of_ne (x 0).property.1 (Ne.symm (fun he => hu (Subtype.ext he)))
  have hvp : (0:ℝ)<x 1 := lt_of_le_of_ne (x 1).property.1 (Ne.symm (fun he => hv (Subtype.ext he)))
  rw [marshallOlkin_cdf_min,marshallOlkin_cdf_min]
  apply min_le_min
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge hup (x 0).property.2 (sub_le_sub_left (show (α:ℝ)≤α' from ha) 1)) (x 1).property.1
  · exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hvp (x 1).property.2 (sub_le_sub_left (show (β:ℝ)≤β' from hb) 1)) (x 0).property.1

theorem marshallOlkin_schurBoth_mono {α β α' β' : I} (ha : α≤α') (hb : β≤β') :
    (marshallOlkin α β).SchurBothLE (marshallOlkin α' β') := by
  constructor
  · exact schurLE_of_lowerOrthantLE_isSI _ _ (marshallOlkin_isSI α β) (marshallOlkin_lowerOrthant_mono ha hb)
  · rw [marshallOlkin_transpose,marshallOlkin_transpose]
    exact schurLE_of_lowerOrthantLE_isSI _ _ (marshallOlkin_isSI β α) (marshallOlkin_lowerOrthant_mono hb ha)

end Verification
