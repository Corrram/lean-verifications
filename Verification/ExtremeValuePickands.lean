import Copula.ExtremeValue.Basic
import Copula.CDF.Bounds
import Copula.Order.Orthant
import Copula.Dependence.Basic
import Copula.OrdinalSum.Basic

/-! # Canonical Pickands functions and exact extreme-value CDF order

The function is recovered from an actual max-stable copula. No density,
smoothness, or pre-assumed ordering of generators is required.
-/

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

noncomputable def unitNegExp (x : ℝ) (hx : 0 ≤ x) : I :=
  ⟨Real.exp (-x), (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by linarith)⟩

noncomputable def pickandsRay (t : I) : Fin 2 → I :=
  ![unitNegExp ((1-(t:ℝ))/2) (by linarith [t.property.2]),
    unitNegExp ((t:ℝ)/2) (by linarith [t.property.1])]

theorem pickandsRay_cdf_pos (C : Copula 2) (t : I) : 0 < C.cdf (pickandsRay t) := by
  have h : (pickandsRay t 0:ℝ)+(pickandsRay t 1:ℝ)-2+1 ≤ C.cdf (pickandsRay t) := by
    simpa only [Fin.sum_univ_two,Nat.cast_ofNat] using C.sum_sub_dim_add_one_le_cdf (pickandsRay t)
  change Real.exp (-((1-(t:ℝ))/2))+Real.exp (-((t:ℝ)/2))-2+1 ≤ C.cdf (pickandsRay t) at h
  have h₁ := Real.add_one_le_exp (-((1-(t:ℝ))/2))
  have h₂ := Real.add_one_le_exp (-((t:ℝ)/2))
  linarith

/-- The usual Pickands function, evaluated on a ray with logarithmic radius one half. -/
noncomputable def copulaPickands (C : Copula 2) (t : I) : ℝ :=
  -2*Real.log (C.cdf (pickandsRay t))

theorem extremeValue_exp_coordinates (C : Copula 2) (hC : C.IsExtremeValue)
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : 0 < x+y) :
    C.cdf ![unitNegExp x hx,unitNegExp y hy] =
      Real.exp (-(x+y)*copulaPickands C ⟨y/(x+y),div_nonneg hy hxy.le,
        (div_le_one hxy).mpr (by linarith)⟩) := by
  let t : I := ⟨y/(x+y),div_nonneg hy hxy.le,(div_le_one hxy).mpr (by linarith)⟩
  have hr : 0 < 2*(x+y) := by positivity
  have he : (fun i => unitPower (pickandsRay t i) (2*(x+y)) hr.le) =
      ![unitNegExp x hx,unitNegExp y hy] := by
    funext i
    apply Subtype.ext
    fin_cases i
    · change Real.exp (-((1-(t:ℝ))/2)) ^ (2*(x+y)) = Real.exp (-x)
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      dsimp [t]
      field_simp
      ring
    · change Real.exp (-((t:ℝ)/2)) ^ (2*(x+y)) = Real.exp (-y)
      rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      congr 1
      dsimp [t]
      field_simp
  have hh := hC (pickandsRay t) (2*(x+y)) hr
  rw [he,Real.rpow_def_of_pos (pickandsRay_cdf_pos C t)] at hh
  rw [hh]
  congr 1
  unfold copulaPickands
  ring

theorem copulaPickands_zero (C : Copula 2) : copulaPickands C 0=1 := by
  have he : unitNegExp (0:ℝ) (by norm_num)=1 := by apply Subtype.ext; simp [unitNegExp]
  unfold copulaPickands pickandsRay
  simp only [Set.Icc.coe_zero,sub_zero,zero_div,he,Copula.cdf_two_one_right]
  simp only [unitNegExp,Real.log_exp]
  norm_num

theorem copulaPickands_one (C : Copula 2) : copulaPickands C 1=1 := by
  have he : unitNegExp (0:ℝ) (by norm_num)=1 := by apply Subtype.ext; simp [unitNegExp]
  unfold copulaPickands pickandsRay
  simp only [Set.Icc.coe_one,sub_self,zero_div,he,Copula.cdf_two_one_left]
  simp only [unitNegExp,Real.log_exp]
  norm_num

/-- Theorem 3.4(i)-(ii), with the Pickands function extracted from max-stability. -/
theorem extremeValue_lowerOrthant_iff_pickands (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    C.LowerOrthantLE D ↔ ∀ t : I, copulaPickands D t ≤ copulaPickands C t := by
  constructor
  · intro h t
    have hh := Real.log_le_log (pickandsRay_cdf_pos C t) (h (pickandsRay t))
    unfold copulaPickands
    linarith
  · intro h z
    let u := z 0
    let v := z 1
    have hz : z=![u,v] := by funext i; fin_cases i <;> rfl
    rw [hz]
    by_cases hu : u=0
    · simp [hu]
    by_cases hv : v=0
    · simp [hv]
    by_cases hu1 : u=1
    · simp [hu1]
    have hup : (0:ℝ)<u := lt_of_le_of_ne u.property.1 (Ne.symm (fun he => hu (Subtype.ext he)))
    have hvp : (0:ℝ)<v := lt_of_le_of_ne v.property.1 (Ne.symm (fun he => hv (Subtype.ext he)))
    have hul : (u:ℝ)<1 := lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he))
    have hux : 0 ≤ -Real.log (u:ℝ) := neg_nonneg.mpr (Real.log_nonpos u.property.1 u.property.2)
    have hvy : 0 ≤ -Real.log (v:ℝ) := neg_nonneg.mpr (Real.log_nonpos v.property.1 v.property.2)
    have hsum : 0 < -Real.log (u:ℝ)+ -Real.log (v:ℝ) := by
      have hh := Real.log_neg hup hul
      linarith
    have hue : unitNegExp (-Real.log (u:ℝ)) hux=u := by
      apply Subtype.ext
      simp only [unitNegExp,neg_neg,Real.exp_log hup]
    have hve : unitNegExp (-Real.log (v:ℝ)) hvy=v := by
      apply Subtype.ext
      simp only [unitNegExp,neg_neg,Real.exp_log hvp]
    rw [← hue,← hve,extremeValue_exp_coordinates C hC _ _ hux hvy hsum,
      extremeValue_exp_coordinates D hD _ _ hux hvy hsum]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (h _) (by linarith)

/-- The open-interval formulation in the paper is equivalent, because both endpoints equal one. -/
theorem extremeValue_lowerOrthant_iff_pickands_interior (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    C.LowerOrthantLE D ↔ ∀ t : I, 0<t → t<1 → copulaPickands D t ≤ copulaPickands C t := by
  rw [extremeValue_lowerOrthant_iff_pickands C D hC hD]
  constructor
  · exact fun h t _ _ => h t
  · intro h t
    by_cases ht0 : t=0
    · simp [ht0,copulaPickands_zero]
    by_cases ht1 : t=1
    · simp [ht1,copulaPickands_one]
    exact h t (lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0))
      (lt_of_le_of_ne (unitInterval.le_one t) ht1)

end Verification
