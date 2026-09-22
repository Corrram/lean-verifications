import Verification.CuadrasAugeSingular

/-! # The exact density-TP2 domain of Marshall–Olkin copulas -/

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem unitPower_powerSample (a : I) (ha : 0<a) (u : I) :
    unitPower (powerSample a u) a a.property.1=u := by
  have ha0 : a≠0 := ne_of_gt ha
  unfold powerSample
  rw [ite_eq_right ha0,unitPower_mul]
  have hae : (a:ℝ)≠0 := ne_of_gt (show (0:ℝ)<a from ha)
  simp only [inv_mul_cancel₀ hae,unitPower_one]

noncomputable def shockCurve (α β : I) : Set (Fin 2 → I) :=
  {x | unitPower (x 0) α α.property.1=unitPower (x 1) β β.property.1}

theorem shockCurve_measurable (α β : I) : MeasurableSet (shockCurve α β) :=
  measurableSet_eq_fun ((measurable_unitPower α α.property.1).comp (measurable_pi_apply 0))
    ((measurable_unitPower β β.property.1).comp (measurable_pi_apply 1))

theorem shockCurve_volume_zero (α β : I) (hβ : 0<β) :
    (volume : Measure (Fin 2 → I)) (shockCurve α β)=0 := by
  let S : Set (I × I) := {p | unitPower p.1 α α.property.1=unitPower p.2 β β.property.1}
  have hS : MeasurableSet S := measurableSet_eq_fun ((measurable_unitPower α α.property.1).comp measurable_fst)
    ((measurable_unitPower β β.property.1).comp measurable_snd)
  have hz : ((volume : Measure I).prod volume) S=0 := by
    apply Measure.measure_prod_null_of_ae_null hS
    exact Filter.Eventually.of_forall fun u => by
      apply Set.Subsingleton.measure_zero
      intro v hv w hw
      apply Subtype.ext
      exact (Real.rpow_left_inj v.property.1 w.property.1 (ne_of_gt (show (0:ℝ)<β from hβ))).mp
        (congrArg (fun z : I => (z:ℝ)) (hv.symm.trans hw))
  have hh := (measurePreserving_finTwoArrow (volume : Measure I)).measure_preimage hS.nullMeasurableSet
  exact hh.trans hz

/-- The common shock charges a Lebesgue-null power curve whenever both weights are positive. -/
theorem marshallOlkin_shockCurve_ne_zero (α β : I) (hα : 0<α) (hβ : 0<β) :
    (marshallOlkin α β).toMeasure (shockCurve α β)≠0 := by
  let ta := unitPower unitHalf α α.property.1
  let tb := unitPower unitHalf β β.property.1
  let t := max ta tb
  let sa := unitPower unitHalf (unitInterval.symm α) (unitInterval.symm α).property.1
  let sb := unitPower unitHalf (unitInterval.symm β) (unitInterval.symm β).property.1
  let A : Set (Fin 2 → I) := {x | x 0=x 1 ∧ t≤x 0}
  let B : Set (Fin 2 → I) := Iic ![sa,sb]
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)).inter
      (measurableSet_le measurable_const (measurable_subtype_coe.comp (measurable_pi_apply 0)))
  have hta : ta<1 :=
    Real.rpow_lt_one (by norm_num [unitHalf]) (by norm_num [unitHalf]) (show (0:ℝ)<α from hα)
  have htb : tb<1 :=
    Real.rpow_lt_one (by norm_num [unitHalf]) (by norm_num [unitHalf]) (show (0:ℝ)<β from hβ)
  have ht : (t:ℝ)<1 := max_lt hta htb
  have hsa : 0<(sa:ℝ) := Real.rpow_pos_of_pos (by norm_num [unitHalf]) _
  have hsb : 0<(sb:ℝ) := Real.rpow_pos_of_pos (by norm_num [unitHalf]) _
  have hmA : (comonotonic 2).toMeasure A≠0 := by
    rw [toMeasure_comonotonic,Measure.map_apply (by fun_prop) hA]
    have he : (fun u : I => fun _ : Fin 2 => u) ⁻¹' A=Ici t := by ext u; simp [A]
    rw [he,unitInterval.volume_Ici]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)).ne'
  have hmB : (independence 2).toMeasure B≠0 := by
    have hh : 0<(independence 2).cdf ![sa,sb] := by
      simp only [cdf_independence,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      positivity
    intro hz
    change 0<((independence 2).toMeasure B).toReal at hh
    rw [hz] at hh
    simp at hh
  have hsub : A ×ˢ B ⊆ maxProductPoint ![α,β] ⁻¹' shockCurve α β := by
    intro p hp
    have hca : unitHalf≤powerSample α (p.1 0) := by
      rw [← powerSample_unitPower α hα unitHalf]
      exact powerSample_mono α ((le_max_left ta tb).trans hp.1.2)
    have hcb : unitHalf≤powerSample β (p.1 1) := by
      rw [← hp.1.1,← powerSample_unitPower β hβ unitHalf]
      exact powerSample_mono β ((le_max_right ta tb).trans hp.1.2)
    have hna : powerSample (unitInterval.symm α) (p.2 0)≤unitHalf :=
      (powerSample_le_iff _ _ _).mpr (hp.2 0)
    have hnb : powerSample (unitInterval.symm β) (p.2 1)≤unitHalf :=
      (powerSample_le_iff _ _ _).mpr (hp.2 1)
    change unitPower (max (powerSample α (p.1 0)) (powerSample (unitInterval.symm α) (p.2 0))) α _ =
      unitPower (max (powerSample β (p.1 1)) (powerSample (unitInterval.symm β) (p.2 1))) β _
    rw [max_eq_left (hna.trans hca),max_eq_left (hnb.trans hcb),
      unitPower_powerSample α hα,unitPower_powerSample β hβ]
    exact hp.1.1
  intro hz
  have hm : ((comonotonic 2).toMeasure.prod (independence 2).toMeasure)
      (maxProductPoint ![α,β] ⁻¹' shockCurve α β)=0 := by
    change (((comonotonic 2).toMeasure.prod (independence 2).toMeasure).map (maxProductPoint ![α,β])) (shockCurve α β)=0 at hz
    rwa [Measure.map_apply (measurable_maxProductPoint _) (shockCurve_measurable α β)] at hz
  have hzero := measure_mono (μ := (comonotonic 2).toMeasure.prod (independence 2).toMeasure) hsub
  rw [hm,Measure.prod_prod] at hzero
  exact (mul_ne_zero hmA hmB) (le_antisymm hzero bot_le)

theorem marshallOlkin_zero_left (β : I) : marshallOlkin 0 β=independence 2 := by
  apply Copula.ext_cdf
  intro x
  have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  by_cases hv : x 1=0
  · simp [hv]
  have hvp : (0:ℝ)<x 1 := lt_of_le_of_ne (x 1).property.1 (Ne.symm (fun he => hv (Subtype.ext he)))
  rw [cdf_marshallOlkin,cdf_independence]
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Set.Icc.coe_zero,
    Real.rpow_zero,sub_zero,Real.rpow_one]
  rw [min_eq_right (Real.rpow_le_one (x 1).property.1 (x 1).property.2 β.property.1),mul_left_comm,
    ← Real.rpow_add hvp]
  simp

theorem marshallOlkin_zero_right (α : I) : marshallOlkin α 0=independence 2 := by
  rw [← marshallOlkin_transpose 0 α,marshallOlkin_zero_left]
  apply Copula.ext_cdf
  intro x
  have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx,Copula.cdf_transpose]
  simp [cdf_independence,Fin.prod_univ_two,mul_comm]

theorem marshallOlkin_absolutelyContinuous_iff (α β : I) :
    (marshallOlkin α β).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ α=0 ∨ β=0 := by
  constructor
  · intro h
    by_contra hn
    have ha : (0:I)<α := lt_of_le_of_ne (unitInterval.nonneg α) (Ne.symm (not_or.mp hn).1)
    have hb : (0:I)<β := lt_of_le_of_ne (unitInterval.nonneg β) (Ne.symm (not_or.mp hn).2)
    exact marshallOlkin_shockCurve_ne_zero α β ha hb (h (shockCurve_volume_zero α β hb))
  · rintro (rfl | rfl)
    · rw [marshallOlkin_zero_left]
      exact Measure.AbsolutelyContinuous.rfl
    · rw [marshallOlkin_zero_right]
      exact Measure.AbsolutelyContinuous.rfl

theorem marshallOlkin_density_tp2_iff (α β : I) :
    (marshallOlkin α β).HasMTP2Density ↔ α=0 ∨ β=0 := by
  constructor
  · exact fun h => (marshallOlkin_absolutelyContinuous_iff α β).mp h.absolutelyContinuous
  · rintro (rfl | rfl)
    · rw [marshallOlkin_zero_left]
      exact hasMTP2Density_independence 2
    · rw [marshallOlkin_zero_right]
      exact hasMTP2Density_independence 2

end Verification
