import Verification.MarshallOlkinXi
import Verification.KendallConditionalProduct
import Verification.MarshallOlkinOrder
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-! # Kendall tau of the two-parameter Marshall–Olkin family -/

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval

namespace Verification

private theorem tau_integrable_unit_rpow (p : ℝ) (hp : -1 < p) :
    Integrable (fun u : I => (u : ℝ) ^ p) := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ p) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hi' : Integrable (fun x : ℝ => x ^ p)
      (volume.restrict (Icc 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi
  exact (unitInterval.measurePreserving_coe.integrable_comp_emb
    unitInterval.measurableEmbedding_coe).mpr hi'

private theorem tau_integral_unit_rpow (p : ℝ) (hp : -1 < p) :
    (∫ u : I, (u : ℝ) ^ p) = 1 / (p + 1) := by
  rw [Copula.integral_unitInterval (fun t : ℝ => t ^ p),
    integral_rpow (Or.inl hp)]
  simp only [Real.one_rpow, Real.zero_rpow (show p + 1 ≠ 0 by linarith), sub_zero]

private theorem tau_integral_unit_Iic_rpow (p : ℝ) (hp : -1 < p) (v : I) :
    (∫ u in Iic v, (u : ℝ) ^ p) = (v : ℝ) ^ (p + 1) / (p + 1) := by
  rw [Copula.integral_unit_Iic (fun t : ℝ => t ^ p) v,
    integral_rpow (Or.inl hp)]
  simp only [Real.zero_rpow (show p + 1 ≠ 0 by linarith), sub_zero]


private noncomputable def moTauSwitch (α β u : I) (hb : 0 < (β : ℝ)) : I :=
  ⟨(u : ℝ) ^ ((α : ℝ) / (β : ℝ)),
    Real.rpow_nonneg u.property.1 _,
    Real.rpow_le_one u.property.1 u.property.2 (div_nonneg α.property.1 hb.le)⟩

private theorem moTauSwitch_power (α β u : I) (hb : 0 < (β : ℝ)) :
    ((moTauSwitch α β u hb : I) : ℝ) ^ (β : ℝ) = (u : ℝ) ^ (α : ℝ) := by
  change ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ (β : ℝ) = (u : ℝ) ^ (α : ℝ)
  rw [← Real.rpow_mul u.property.1]
  congr 1
  exact div_mul_cancel₀ _ hb.ne'

private theorem moTauSwitch_lt_iff (α β u v : I) (hb : 0 < (β : ℝ)) :
    (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) ↔ moTauSwitch α β u hb < v := by
  change (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) ↔
    ((moTauSwitch α β u hb : I) : ℝ) < (v : ℝ)
  rw [← moTauSwitch_power α β u hb]
  exact Real.rpow_lt_rpow_iff (moTauSwitch α β u hb).property.1 v.property.1 hb

private theorem moTauSwitch_gt_iff (α β u v : I) (hb : 0 < (β : ℝ)) :
    (v : ℝ) ^ (β : ℝ) < (u : ℝ) ^ (α : ℝ) ↔ v < moTauSwitch α β u hb := by
  change (v : ℝ) ^ (β : ℝ) < (u : ℝ) ^ (α : ℝ) ↔
    (v : ℝ) < ((moTauSwitch α β u hb : I) : ℝ)
  rw [← moTauSwitch_power α β u hb]
  exact Real.rpow_lt_rpow_iff v.property.1 (moTauSwitch α β u hb).property.1 hb

private noncomputable def moCrossConditional (α β u v : I) : ℝ :=
  marshallOlkinConditional α β u v * marshallOlkinConditional β α v u

private theorem moCrossConditional_eq_piecewise (α β u v : I)
    (hu : 0 < (u : ℝ)) (hb : 0 < (β : ℝ))
    (hne : v ≠ moTauSwitch α β u hb) :
    moCrossConditional α β u v =
      if moTauSwitch α β u hb < v then
        (1 - (β : ℝ)) * (u : ℝ) * (v : ℝ) ^ (1 - 2 * (β : ℝ))
      else (1 - (α : ℝ)) * (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (v : ℝ) := by
  let t := moTauSwitch α β u hb
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hp : (v : ℝ) ^ (β : ℝ) < (u : ℝ) ^ (α : ℝ) :=
      (moTauSwitch_gt_iff α β u v hb).mpr hlt
    have hnot : ¬ (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) := not_lt.mpr hp.le
    rw [moCrossConditional, marshallOlkinConditional,
      ite_eq_right hnot, marshallOlkinConditional, ite_eq_left hp,
      ite_eq_right (not_lt.mpr hlt.le)]
    calc
      _ = (1 - (α : ℝ)) *
          ((u : ℝ) ^ (-(α : ℝ)) * (u : ℝ) ^ (1 - (α : ℝ))) * (v : ℝ) := by ring
      _ = _ := by
        rw [← Real.rpow_add hu]
        congr 2
        ring_nf
  · have hp : (u : ℝ) ^ (α : ℝ) < (v : ℝ) ^ (β : ℝ) :=
      (moTauSwitch_lt_iff α β u v hb).mpr hgt
    have hnot : ¬ (v : ℝ) ^ (β : ℝ) < (u : ℝ) ^ (α : ℝ) := not_lt.mpr hp.le
    have hv : 0 < (v : ℝ) := lt_of_le_of_lt t.property.1 hgt
    rw [moCrossConditional, marshallOlkinConditional, ite_eq_left hp,
      marshallOlkinConditional, ite_eq_right hnot, ite_eq_left hgt]
    calc
      _ = (1 - (β : ℝ)) * (u : ℝ) *
          ((v : ℝ) ^ (1 - (β : ℝ)) * (v : ℝ) ^ (-(β : ℝ))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hv]
        congr 1
        ring_nf

private theorem integral_moCrossConditional_response_lt_one (α β u : I)
    (hu : 0 < u) (hb : 0 < (β : ℝ)) (hb1 : (β : ℝ) < 1) :
    (∫ v : I, moCrossConditional α β u v) =
      (u : ℝ) / 2 - (α : ℝ) / 2 *
        (u : ℝ) ^ (1 + 2 * (α : ℝ) * (1 - (β : ℝ)) / (β : ℝ)) := by
  classical
  let t := moTauSwitch α β u hb
  let p : ℝ := 1 - 2 * (β : ℝ)
  let q : ℝ := 1 + 2 * (α : ℝ) * (1 - (β : ℝ)) / (β : ℝ)
  let f : I → ℝ := fun v =>
    if t < v then (1 - (β : ℝ)) * (u : ℝ) * (v : ℝ) ^ p
    else (1 - (α : ℝ)) * (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (v : ℝ)
  have hp : -1 < p := by dsimp [p]; linarith
  have hpow : Integrable (fun v : I => (v : ℝ) ^ p) :=
    tau_integrable_unit_rpow p hp
  have hid : Integrable (fun v : I => (v : ℝ)) :=
    Copula.integrable_continuous_unit volume continuous_subtype_val
  have hf : Integrable f := by
    change Integrable (fun v : I => if t < v then
      (1 - (β : ℝ)) * (u : ℝ) * (v : ℝ) ^ p else
      (1 - (α : ℝ)) * (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (v : ℝ))
    exact Integrable.piecewise (s := Ioi t) measurableSet_Ioi
      (hpow.const_mul _).integrableOn (hid.const_mul _).integrableOn
  have he : (fun v : I => moCrossConditional α β u v) =ᵐ[volume] f := by
    filter_upwards [Measure.ae_ne volume t] with v hv
    exact moCrossConditional_eq_piecewise α β u v
      (show 0 < (u : ℝ) from hu) hb hv
  rw [integral_congr_ae he]
  have hs := integral_add_compl (s := Iic t) measurableSet_Iic hf
  rw [compl_Iic] at hs
  have hq1 : (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (t : ℝ) ^ 2 =
      (u : ℝ) ^ q := by
    change (u : ℝ) ^ (1 - 2 * (α : ℝ)) *
      ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ 2 = _
    rw [← Real.rpow_mul_natCast u.property.1,
      ← Real.rpow_add (show (0 : ℝ) < u from hu)]
    congr 1
    dsimp [q]
    field_simp
    ring
  have hq2 : (u : ℝ) * (t : ℝ) ^ (p + 1) = (u : ℝ) ^ q := by
    change (u : ℝ) * ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ (p + 1) = _
    calc
      _ = (u : ℝ) ^ (1 : ℝ) *
          ((u : ℝ) ^ ((α : ℝ) / (β : ℝ))) ^ (p + 1) := by rw [Real.rpow_one]
      _ = (u : ℝ) ^ (1 : ℝ) *
          (u : ℝ) ^ (((α : ℝ) / (β : ℝ)) * (p + 1)) := by
            rw [Real.rpow_mul u.property.1]
      _ = (u : ℝ) ^ (1 + ((α : ℝ) / (β : ℝ)) * (p + 1)) := by
            rw [Real.rpow_add (show (0 : ℝ) < u from hu)]
      _ = _ := by
            congr 1
            dsimp [p,q]
            field_simp
            ring
  have hl : (∫ v in Iic t, f v) =
      (1 - (α : ℝ)) * (u : ℝ) ^ q / 2 := by
    have hleft_eq : (∫ v in Iic t, f v) =
        ∫ v in Iic t, (1 - (α : ℝ)) *
          (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (v : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro v hv
      change v ≤ t at hv
      dsimp [f]
      rw [ite_eq_right (not_lt.mpr hv)]
    rw [hleft_eq, integral_const_mul,
      Copula.integral_unit_Iic (fun v : ℝ => v) t, integral_id]
    norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero]
    calc
      _ = (1 - (α : ℝ)) *
          ((u : ℝ) ^ (1 - 2 * (α : ℝ)) * (t : ℝ) ^ 2) / 2 := by ring
      _ = _ := by rw [hq1]
  have hrpow : (∫ v in Ioi t, (v : ℝ) ^ p) =
      1 / (p + 1) - (t : ℝ) ^ (p + 1) / (p + 1) := by
    have hh := integral_add_compl (s := Iic t) measurableSet_Iic hpow
    rw [compl_Iic, tau_integral_unit_Iic_rpow p hp t,
      tau_integral_unit_rpow p hp] at hh
    linarith only [hh]
  have hr : (∫ v in Ioi t, f v) =
      (u : ℝ) / 2 - (u : ℝ) ^ q / 2 := by
    have hright_eq : (∫ v in Ioi t, f v) =
        ∫ v in Ioi t, (1 - (β : ℝ)) * (u : ℝ) * (v : ℝ) ^ p := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      change t < v at hv
      dsimp [f]
      rw [ite_eq_left hv]
    rw [hright_eq, integral_const_mul, hrpow]
    have hd : p + 1 = 2 * (1 - (β : ℝ)) := by dsimp [p]; ring
    have hd0 : 1 - (β : ℝ) ≠ 0 := by linarith
    rw [hd]
    field_simp [hd0]
    have heq : (1 - (β : ℝ)) * 2 = p + 1 := by dsimp [p]; ring
    rw [heq, mul_sub, mul_one, hq2]
  rw [hl,hr] at hs
  calc
    _ = (1 - (α : ℝ)) * (u : ℝ) ^ q / 2 +
        ((u : ℝ) / 2 - (u : ℝ) ^ q / 2) := hs.symm
    _ = _ := by dsimp [q]; ring

private theorem integral_moCrossConditional_response_one (α u : I) (hu : 0 < u) :
    (∫ v : I, moCrossConditional α 1 u v) =
      (1 - (α : ℝ)) * (u : ℝ) / 2 := by
  classical
  have hb : 0 < ((1 : I) : ℝ) := by norm_num
  let t := moTauSwitch α 1 u hb
  let f : I → ℝ := fun v => if t < v then 0 else
    (1 - (α : ℝ)) * (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (v : ℝ)
  have ht : (t : ℝ) = (u : ℝ) ^ (α : ℝ) := by
    change (u : ℝ) ^ ((α : ℝ) / (1 : ℝ)) = _
    norm_num
  have hf : Integrable f := by
    change Integrable (fun v : I => if t < v then (0 : ℝ) else
      (1 - (α : ℝ)) * (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (v : ℝ))
    exact Integrable.piecewise (s := Ioi t) measurableSet_Ioi
      (integrable_const 0).integrableOn
      ((Copula.integrable_continuous_unit volume continuous_subtype_val).const_mul _).integrableOn
  have he : (fun v : I => moCrossConditional α 1 u v) =ᵐ[volume] f := by
    filter_upwards [Measure.ae_ne volume t] with v hv
    have hh := moCrossConditional_eq_piecewise α 1 u v
      (show 0 < (u : ℝ) from hu) hb hv
    simpa only [f, Set.Icc.coe_one, sub_self, zero_mul] using hh
  rw [integral_congr_ae he]
  have hs := integral_add_compl (s := Iic t) measurableSet_Iic hf
  rw [compl_Iic] at hs
  have hpow : (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (t : ℝ) ^ 2 = (u : ℝ) := by
    rw [ht, ← Real.rpow_mul_natCast u.property.1,
      ← Real.rpow_add (show (0 : ℝ) < u from hu)]
    convert Real.rpow_one (u : ℝ) using 1
    congr 1
    ring
  have hl : (∫ v in Iic t, f v) =
      (1 - (α : ℝ)) * (u : ℝ) / 2 := by
    have hleft_eq : (∫ v in Iic t, f v) =
        ∫ v in Iic t, (1 - (α : ℝ)) *
          (u : ℝ) ^ (1 - 2 * (α : ℝ)) * (v : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro v hv
      change v ≤ t at hv
      dsimp [f]
      rw [ite_eq_right (not_lt.mpr hv)]
    rw [hleft_eq, integral_const_mul,
      Copula.integral_unit_Iic (fun v : ℝ => v) t, integral_id]
    norm_num only [zero_pow (by decide : 2 ≠ 0), sub_zero]
    calc
      _ = (1 - (α : ℝ)) *
          ((u : ℝ) ^ (1 - 2 * (α : ℝ)) * (t : ℝ) ^ 2) / 2 := by ring
      _ = _ := by rw [hpow]
  have hr : (∫ v in Ioi t, f v) = 0 := by
    have hright_eq : (∫ v in Ioi t, f v) = ∫ v in Ioi t, (0 : ℝ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      change t < v at hv
      dsimp [f]
      rw [ite_eq_left hv]
    rw [hright_eq]
    simp
  rw [hl,hr] at hs
  simpa only [add_zero] using hs.symm

private theorem mo_crossIntegral_eq_explicit (α β : I)
    (ha : 0 < (α : ℝ)) (hb : 0 < (β : ℝ)) :
    (∫ u : I, ∫ v : I,
      (Copula.marshallOlkin α β).conditionalCDF u v *
        (Copula.marshallOlkin β α).conditionalCDF v u) =
      ∫ u : I, ∫ v : I, moCrossConditional α β u v := by
  let C := Copula.marshallOlkin α β
  have hfirst : ∀ᵐ u : I, ∀ᵐ v : I,
      C.conditionalCDF u v = marshallOlkinConditional α β u v :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v u => C.conditionalCDF u v = marshallOlkinConditional α β u v)
      (measurableSet_eq_fun C.measurable_conditionalCDF
        ((marshallOlkinConditional_measurable α β).comp measurable_swap))).mp
      (Eventually.of_forall (conditionalCDF_marshallOlkin α β · ha))
  apply integral_congr_ae
  filter_upwards [hfirst] with u hu
  apply integral_congr_ae
  filter_upwards [hu, conditionalCDF_marshallOlkin β α u hb] with v h1 h2
  dsimp [moCrossConditional]
  rw [h1, h2]

private theorem marshallOlkin_kendallTau_pos_lt_one (α β : I)
    (ha : 0 < (α : ℝ)) (hb : 0 < (β : ℝ)) (hb1 : (β : ℝ) < 1) :
    (Copula.marshallOlkin α β).kendallTau =
      (α : ℝ) * (β : ℝ) /
        ((α : ℝ) + (β : ℝ) - (α : ℝ) * (β : ℝ)) := by
  rw [kendallTau_conditional_product,
    marshallOlkin_transpose α β, mo_crossIntegral_eq_explicit α β ha hb]
  let q : ℝ := 1 + 2 * (α : ℝ) * (1 - (β : ℝ)) / (β : ℝ)
  have he : (∫ u : I, ∫ v : I, moCrossConditional α β u v) =
      ∫ u : I, (u : ℝ) / 2 - (α : ℝ) / 2 * (u : ℝ) ^ q := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0:I)] with u hu
    exact integral_moCrossConditional_response_lt_one α β u
      (lt_of_le_of_ne u.property.1 (Ne.symm hu)) hb hb1
  rw [he]
  have hq : 0 ≤ q := by
    dsimp [q]
    have hpos : 0 ≤ 2 * (α : ℝ) * (1 - (β : ℝ)) / (β : ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) α.property.1)
        (by linarith)) hb.le
    linarith
  have hpow : Integrable (fun u : I => (u : ℝ) ^ q) :=
    Copula.integrable_continuous_unit volume
      ((Real.continuous_rpow_const hq).comp continuous_subtype_val)
  have hid : Integrable (fun u : I => (u : ℝ)) :=
    Copula.integrable_continuous_unit volume continuous_subtype_val
  rw [integral_sub (hid.div_const _) (hpow.const_mul _),
    integral_div, integral_const_mul, Copula.integral_unit_id,
    integral_unit_rpow_nonneg q hq]
  have hb0 : (β : ℝ) ≠ 0 := hb.ne'
  have hD : (α : ℝ) + (β : ℝ) - (α : ℝ) * (β : ℝ) ≠ 0 := by
    have hpos : 0 ≤ (α : ℝ) * (1 - (β : ℝ)) :=
      mul_nonneg α.property.1 (by linarith)
    nlinarith
  have hq0 : q + 1 ≠ 0 := by linarith [hq]
  dsimp [q] at *
  have hD2 : (α : ℝ) * 2 - (α : ℝ) * (β : ℝ) * 2 + (β : ℝ) * 2 ≠ 0 := by
    have heq : (α : ℝ) * 2 - (α : ℝ) * (β : ℝ) * 2 + (β : ℝ) * 2 =
        2 * ((α : ℝ) + (β : ℝ) - (α : ℝ) * (β : ℝ)) := by ring
    rw [heq]
    exact mul_ne_zero (by norm_num) hD
  field_simp [hb0, hD, hq0, hD2]
  linear_combination 4 * (α : ℝ) * (β : ℝ) * (mul_inv_cancel₀ hD2)

private theorem marshallOlkin_kendallTau_one (α : I) (ha : 0 < (α : ℝ)) :
    (Copula.marshallOlkin α 1).kendallTau = (α : ℝ) := by
  have hb : 0 < ((1 : I) : ℝ) := by norm_num
  rw [kendallTau_conditional_product,
    marshallOlkin_transpose α 1, mo_crossIntegral_eq_explicit α 1 ha hb]
  have he : (∫ u : I, ∫ v : I, moCrossConditional α 1 u v) =
      ∫ u : I, (1 - (α : ℝ)) * (u : ℝ) / 2 := by
    apply integral_congr_ae
    filter_upwards [Measure.ae_ne volume (0:I)] with u hu
    exact integral_moCrossConditional_response_one α u
      (lt_of_le_of_ne u.property.1 (Ne.symm hu))
  rw [he, integral_div, integral_const_mul, Copula.integral_unit_id]
  ring

theorem marshallOlkin_kendallTau (α β : I) :
    (Copula.marshallOlkin α β).kendallTau =
      (α : ℝ) * (β : ℝ) /
        ((α : ℝ) + (β : ℝ) - (α : ℝ) * (β : ℝ)) := by
  by_cases hα : (α : ℝ) = 0
  · have ha : α = 0 := Subtype.ext hα
    subst α
    rw [marshallOlkin_zero_left, Copula.kendallTau_independence]
    norm_num
  by_cases hβ : (β : ℝ) = 0
  · have hb : β = 0 := Subtype.ext hβ
    subst β
    rw [marshallOlkin_zero_right, Copula.kendallTau_independence]
    norm_num
  have ha : 0 < (α : ℝ) := lt_of_le_of_ne α.property.1 (Ne.symm hα)
  have hb : 0 < (β : ℝ) := lt_of_le_of_ne β.property.1 (Ne.symm hβ)
  by_cases hβ1 : β = 1
  · subst β
    rw [marshallOlkin_kendallTau_one α ha]
    norm_num
  · exact marshallOlkin_kendallTau_pos_lt_one α β ha hb
      (lt_of_le_of_ne β.property.2 (fun h => hβ1 (Subtype.ext h)))
end Verification
