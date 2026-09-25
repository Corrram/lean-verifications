import Papers.AnsariRockel2024.Galambos
import Verification.ExtremeValueConditional

open ProbabilityTheory MeasureTheory Real Set Filter Copula
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

private theorem kernel_homogeneous (δ : ℝ) (hδ : 0<δ) (t x y : ℝ)
    (ht : 0<t) (hx : 0≤x) (hy : 0≤y) :
    Verification.galambosTailKernel δ (t*x) (t*y)=t*Verification.galambosTailKernel δ x y := by
  unfold Verification.galambosTailKernel
  rw [Real.mul_rpow ht.le hx,Real.mul_rpow ht.le hy,← mul_add,
    Real.mul_rpow (Real.rpow_nonneg ht.le _) (add_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)),
    ← Real.rpow_mul ht.le,show (-δ)*(-1/δ)=1 by field_simp,Real.rpow_one]

theorem galambos_isExtremeValue (δ : ℝ) (hδ : 0<δ) :
    (Verification.galambos δ hδ).IsExtremeValue := by
  intro u t ht
  have hu : u=![u 0,u 1] := by ext i; fin_cases i <;> rfl
  by_cases hz : ∃ i,u i=0
  · obtain ⟨i,hi⟩ := hz
    have hp : unitPower (u i) t ht.le=0 := by ext; simp [hi,Real.zero_rpow ht.ne']
    rw [cdf_eq_zero_of_coord_eq_zero _ _ i hp,cdf_eq_zero_of_coord_eq_zero _ _ i hi,
      Real.zero_rpow ht.ne']
  have hpos (i) : 0<(u i:ℝ) :=
    lt_of_le_of_ne (u i).property.1 (fun h => hz ⟨i,Subtype.ext h.symm⟩)
  by_cases h0 : u 0=1
  · have he (C : Copula 2) : C.cdf u=(u 1:ℝ) := by
      conv_lhs => rw [hu,h0]
      exact cdf_two_one_left _ _
    have hp : (fun i => unitPower (u i) t ht.le)=![1,unitPower (u 1) t ht.le] := by
      ext i; fin_cases i <;> simp [h0]
    rw [hp,cdf_two_one_left,he,coe_unitPower]
  by_cases h1 : u 1=1
  · have he (C : Copula 2) : C.cdf u=(u 0:ℝ) := by
      conv_lhs => rw [hu,h1]
      exact cdf_two_one_right _ _
    have hp : (fun i => unitPower (u i) t ht.le)=![unitPower (u 0) t ht.le,1] := by
      ext i; fin_cases i <;> simp [h1]
    rw [hp,cdf_two_one_right,he,coe_unitPower]
  have hi0 : (u 0:ℝ)∈Ioo (0:ℝ) 1 := ⟨hpos 0,lt_of_le_of_ne (u 0).property.2 (fun h => h0 (Subtype.ext h))⟩
  have hi1 : (u 1:ℝ)∈Ioo (0:ℝ) 1 := ⟨hpos 1,lt_of_le_of_ne (u 1).property.2 (fun h => h1 (Subtype.ext h))⟩
  have hip (v : I) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
      (unitPower v t ht.le:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hv.1 _,Real.rpow_lt_one v.property.1 hv.2 ht⟩
  have hp : (fun i => unitPower (u i) t ht.le)=![unitPower (u 0) t ht.le,unitPower (u 1) t ht.le] := by
    ext i; fin_cases i <;> rfl
  rw [hp,galambos_cdf_interior δ hδ _ _ (hip _ hi0) (hip _ hi1)]
  conv_rhs => rw [hu,galambos_cdf_interior δ hδ _ _ hi0 hi1]
  change (u 0:ℝ)^t*(u 1:ℝ)^t*Real.exp
      (Verification.galambosTailKernel δ (-Real.log ((u 0:ℝ)^t)) (-Real.log ((u 1:ℝ)^t))) =
    ((u 0:ℝ)*(u 1:ℝ)*Real.exp (Verification.galambosTailKernel δ (-Real.log (u 0:ℝ)) (-Real.log (u 1:ℝ))))^t
  simp only [Real.log_rpow (hpos _),neg_mul_eq_mul_neg]
  rw [kernel_homogeneous δ hδ t _ _ ht (by linarith [Real.log_neg hi0.1 hi0.2])
    (by linarith [Real.log_neg hi1.1 hi1.2]),
    Real.mul_rpow (mul_nonneg (u 0).property.1 (u 1).property.1) (Real.exp_pos _).le,
    Real.mul_rpow (u 0).property.1 (u 1).property.1,← Real.exp_mul,mul_comm t]

theorem galambos_isCI (δ : ℝ) (hδ : 0<δ) : (Verification.galambos δ hδ).IsCI :=
  Verification.extremeValue_isCI _ (galambos_isExtremeValue δ hδ)

theorem galambos_pickands_interior (δ : ℝ) (hδ : 0<δ) (t : I)
    (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    Verification.copulaPickands (Verification.galambos δ hδ) t =
      1-((t:ℝ)^(-δ)+(1-(t:ℝ))^(-δ))^(-1/δ) := by
  have hx : 0<(1-(t:ℝ))/2 := by linarith [ht.2]
  have hy : 0<(t:ℝ)/2 := by linarith [ht.1]
  unfold Verification.copulaPickands Verification.pickandsRay
  rw [galambos_cdf_interior δ hδ _ _
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)⟩
    ⟨Real.exp_pos _,Real.exp_lt_one_iff.mpr (neg_neg_of_pos hy)⟩]
  simp only [Verification.unitNegExp,Real.log_exp,neg_neg]
  rw [Real.log_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne',Real.log_exp,Real.log_exp,Real.log_exp]
  have he : (((1-(t:ℝ))/2)^(-δ)+((t:ℝ)/2)^(-δ))^(-1/δ)=
      (1/2:ℝ)*Verification.galambosTailKernel δ (1-(t:ℝ)) (t:ℝ) := by
    change Verification.galambosTailKernel δ ((1-(t:ℝ))/2) ((t:ℝ)/2)=_
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using kernel_homogeneous δ hδ (1/2) (1-(t:ℝ)) (t:ℝ) (by norm_num) (by linarith [ht.2]) ht.1.le
  rw [he]
  unfold Verification.galambosTailKernel
  rw [add_comm ((1-(t:ℝ))^(-δ))]
  ring

end Papers.AnsariRockel2024
