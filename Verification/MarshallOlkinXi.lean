import Verification.MarshallOlkinConditional

/-! # Chatterjee xi of the two-parameter Marshall–Olkin family -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval

namespace Verification

private noncomputable def moXiSwitch (α β u : I) (hb : 0 < (β : ℝ)) : I :=
  ⟨(u : ℝ) ^ ((α : ℝ) / (β : ℝ)),
    Real.rpow_nonneg u.property.1 _,
    Real.rpow_le_one u.property.1 u.property.2 (div_nonneg α.property.1 hb.le)⟩

private theorem moXiSwitch_power (α β u : I) (hb : 0 < (β : ℝ)) :
    ((moXiSwitch α β u hb : I) : ℝ) ^ (β : ℝ) = (u : ℝ) ^ (α : ℝ) := by
  change ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ (β : ℝ) = (u : ℝ) ^ (α : ℝ)
  rw [← Real.rpow_mul u.property.1]
  congr 1
  exact div_mul_cancel₀ _ hb.ne'

private theorem moXiSwitch_lt_iff (α β u v : I) (hb : 0 < (β : ℝ)) :
    (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) ↔ moXiSwitch α β u hb < v := by
  change (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) ↔
    ((moXiSwitch α β u hb : I) : ℝ) < (v : ℝ)
  rw [← moXiSwitch_power α β u hb]
  exact Real.rpow_lt_rpow_iff (moXiSwitch α β u hb).property.1 v.property.1 hb

theorem integral_marshallOlkinConditional_sq_response (α β u : I)
    (hu : 0 < u) (hb : 0 < (β : ℝ)) :
    (∫ v : I, marshallOlkinConditional α β u v ^ 2) =
      (1 - (α : ℝ)) ^ 2 *
        (u : ℝ) ^ ((α : ℝ) * (3 - 2 * (β : ℝ)) / (β : ℝ)) / 3 +
      (1 - (u : ℝ) ^ ((α : ℝ) * (3 - 2 * (β : ℝ)) / (β : ℝ))) /
        (3 - 2 * (β : ℝ)) := by
  classical
  let t := moXiSwitch α β u hb
  let p : ℝ := 1 - (β : ℝ)
  have hp : 0 ≤ p := by dsimp [p]; linarith [β.property.2]
  have hp2 : 0 ≤ 2 * p := by positivity
  have hpow : Integrable (fun v : I => (v : ℝ) ^ (2 * p)) :=
    Copula.integrable_continuous_unit volume
      ((Real.continuous_rpow_const hp2).comp continuous_subtype_val)
  have he (v : I) : marshallOlkinConditional α β u v ^ 2 =
      if t < v then (v : ℝ) ^ (2 * p)
      else ((1 - (α : ℝ)) * (u : ℝ) ^ (-(α : ℝ))) ^ 2 * (v : ℝ) ^ 2 := by
    by_cases h : (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ)
    · have ht : t < v := (moXiSwitch_lt_iff α β u v hb).mp h
      simp only [marshallOlkinConditional, ite_eq_left h, ite_eq_left ht]
      rw [← Real.rpow_mul_natCast v.property.1]
      congr 1
      dsimp [p]
      ring
    · have ht : ¬ t < v := (moXiSwitch_lt_iff α β u v hb).not.mp h
      simp only [marshallOlkinConditional, ite_eq_right h, ite_eq_right ht]
      ring
  have hi : Integrable (fun v : I => marshallOlkinConditional α β u v ^ 2) := by
    simp_rw [he]
    have hg : Integrable (fun v : I =>
        ((1 - (α : ℝ)) * (u : ℝ) ^ (-(α : ℝ))) ^ 2 * (v : ℝ) ^ 2) :=
      Copula.integrable_continuous_unit volume (by fun_prop)
    exact Integrable.piecewise (s := Ioi t) measurableSet_Ioi
      hpow.integrableOn hg.integrableOn
  have hs := integral_add_compl (s := Iic t) measurableSet_Iic hi
  rw [compl_Iic] at hs
  have hl : (∫ v in Iic t, marshallOlkinConditional α β u v ^ 2) =
      (1 - (α : ℝ)) ^ 2 *
        (u : ℝ) ^ ((α : ℝ) * (3 - 2 * (β : ℝ)) / (β : ℝ)) / 3 := by
    have hleft_eq : (∫ v in Iic t, marshallOlkinConditional α β u v ^ 2) =
        ∫ v in Iic t, ((1 - (α : ℝ)) * (u : ℝ) ^ (-(α : ℝ))) ^ 2 * (v : ℝ) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro v hv
      change v ≤ t at hv
      change marshallOlkinConditional α β u v ^ 2 = _
      rw [he, ite_eq_right (not_lt.mpr hv)]
    rw [hleft_eq, integral_const_mul,
      Copula.integral_unit_Iic (fun v : ℝ => v ^ 2) t, integral_pow]
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,zero_pow (by decide : 3 ≠ 0),sub_zero]
    have hh : ((u : ℝ) ^ (-(α : ℝ))) ^ 2 * (t : ℝ) ^ 3 =
        (u : ℝ) ^ ((α : ℝ) * (3 - 2 * (β : ℝ)) / (β : ℝ)) := by
      change ((u : ℝ) ^ (-(α : ℝ))) ^ 2 *
        ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ 3 = _
      rw [← Real.rpow_mul_natCast u.property.1,
        ← Real.rpow_mul_natCast u.property.1,
        ← Real.rpow_add (show (0 : ℝ) < u from hu)]
      congr 1
      field_simp
      ring
    calc
      _ = (1 - (α : ℝ)) ^ 2 *
          (((u : ℝ) ^ (-(α : ℝ))) ^ 2 * (t : ℝ) ^ 3) / 3 := by ring
      _ = _ := by rw [hh]
  have hr : (∫ v in Ioi t, marshallOlkinConditional α β u v ^ 2) =
      (1 - (u : ℝ) ^ ((α : ℝ) * (3 - 2 * (β : ℝ)) / (β : ℝ))) /
        (3 - 2 * (β : ℝ)) := by
    have hright_eq : (∫ v in Ioi t, marshallOlkinConditional α β u v ^ 2) =
        ∫ v in Ioi t, (v : ℝ) ^ (2 * p) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      change t < v at hv
      change marshallOlkinConditional α β u v ^ 2 = _
      rw [he, ite_eq_left hv]
    rw [hright_eq]
    have hh := integral_add_compl (s := Iic t) measurableSet_Iic hpow
    rw [compl_Iic, integral_unit_Iic_rpow_nonneg _ hp2,
      integral_unit_rpow_nonneg _ hp2] at hh
    have hd : 2 * p + 1 = 3 - 2 * (β : ℝ) := by dsimp [p]; ring
    rw [hd] at hh
    have heq : (t : ℝ) ^ (3 - 2 * (β : ℝ)) =
        (u : ℝ) ^ ((α : ℝ) * (3 - 2 * (β : ℝ)) / (β : ℝ)) := by
      change ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ _ = _
      rw [← Real.rpow_mul u.property.1]
      congr 1
      field_simp
    rw [heq] at hh
    rw [sub_div]
    linarith only [hh]
  rw [hl,hr] at hs
  exact hs.symm

theorem marshallOlkin_chatterjeeXi_pos (α β : I)
    (ha : 0 < (α : ℝ)) (hb : 0 < (β : ℝ)) :
    (Copula.marshallOlkin α β).chatterjeeXi =
      2 * (α : ℝ) ^ 2 * (β : ℝ) /
        (3 * (α : ℝ) + (β : ℝ) - 2 * (α : ℝ) * (β : ℝ)) := by
  have he (v : I) :
      (∫ u : I, (Copula.marshallOlkin α β).conditionalCDF u v ^ 2) =
        ∫ u : I, marshallOlkinConditional α β u v ^ 2 :=
    integral_congr_ae ((conditionalCDF_marshallOlkin α β v ha).fun_comp (fun z => z ^ 2))
  unfold Copula.chatterjeeXi
  simp_rw [he]
  rw [integral_integral_swap (marshallOlkinConditional_sq_joint_integrable α β ha)]
  let q : ℝ := (α : ℝ) * (3 - 2 * (β : ℝ)) / (β : ℝ)
  have he' : (∫ u : I, ∫ v : I, marshallOlkinConditional α β u v ^ 2) =
      ∫ u : I, (1 - (α : ℝ)) ^ 2 * (u : ℝ) ^ q / 3 +
        (1 - (u : ℝ) ^ q) / (3 - 2 * (β : ℝ)) := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0:I)] with u hu
    exact integral_marshallOlkinConditional_sq_response α β u
      (lt_of_le_of_ne u.property.1 (Ne.symm hu)) hb
  rw [he']
  have hq : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (mul_nonneg α.property.1 (by linarith [β.property.2])) hb.le
  have hpow : Integrable (fun u : I => (u : ℝ) ^ q) :=
    Copula.integrable_continuous_unit volume
      ((Real.continuous_rpow_const hq).comp continuous_subtype_val)
  rw [integral_add (f := fun u : I =>
      (1 - (α : ℝ)) ^ 2 * (u : ℝ) ^ q / 3)
      (g := fun u : I =>
        (1 - (u : ℝ) ^ q) / (3 - 2 * (β : ℝ)))
      ((hpow.const_mul _).div_const _)
      (((integrable_const _).sub hpow).div_const _),
    integral_div, integral_div, integral_const_mul,
    integral_sub (integrable_const (1 : ℝ)) hpow,
    integral_unit_rpow_nonneg q hq]
  simp only [integral_const, probReal_univ, one_smul]
  have hb0 : (β : ℝ) ≠ 0 := hb.ne'
  have hd : 3 - 2 * (β : ℝ) ≠ 0 := by linarith [β.property.2]
  have hq0 : q + 1 ≠ 0 := by linarith [hq]
  have hD : 3 * (α : ℝ) + (β : ℝ) - 2 * (α : ℝ) * (β : ℝ) ≠ 0 := by
    have hpos : 0 ≤ (α : ℝ) * (3 - 2 * (β : ℝ)) :=
      mul_nonneg α.property.1 (by linarith [β.property.2])
    nlinarith
  dsimp [q] at *
  have hD' : (α : ℝ) * 3 - (α : ℝ) * (β : ℝ) * 2 + (β : ℝ) ≠ 0 := by
    convert hD using 1; ring
  field_simp [hb0, hd, hq0, hD, hD']
  linear_combination -12 * (β : ℝ) * (mul_inv_cancel₀ hD')
theorem marshallOlkin_chatterjeeXi (α β : I) :
    (Copula.marshallOlkin α β).chatterjeeXi =
      2 * (α : ℝ) ^ 2 * (β : ℝ) /
        (3 * (α : ℝ) + (β : ℝ) - 2 * (α : ℝ) * (β : ℝ)) := by
  by_cases hα : (α : ℝ) = 0
  · have ha : α = 0 := Subtype.ext hα
    subst α
    rw [marshallOlkin_zero_left, Copula.chatterjeeXi_independence]
    norm_num
  by_cases hβ : (β : ℝ) = 0
  · have hb : β = 0 := Subtype.ext hβ
    subst β
    rw [marshallOlkin_zero_right, Copula.chatterjeeXi_independence]
    norm_num
  exact marshallOlkin_chatterjeeXi_pos α β
    (lt_of_le_of_ne α.property.1 (Ne.symm hα))
    (lt_of_le_of_ne β.property.1 (Ne.symm hβ))
end Verification
