import Verification.MarshallOlkinOrder
import Copula.Dependence.Singular

/-! # Singular mass and the exact density-TP2 classification of Cuadras–Augé -/

open MeasureTheory ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem powerSample_mono (a : I) : Monotone (powerSample a) := by
  intro u v huv
  unfold powerSample
  split_ifs
  · exact le_rfl
  · exact Real.rpow_le_rpow u.property.1 huv (inv_nonneg.mpr a.property.1)

theorem powerSample_unitPower (a : I) (ha : 0<a) (u : I) :
    powerSample a (unitPower u a a.property.1)=u := by
  have ha0 : a≠0 := ne_of_gt ha
  unfold powerSample
  rw [ite_eq_right ha0,unitPower_mul]
  have hae : (a:ℝ)≠0 := ne_of_gt (show (0:ℝ)<a from ha)
  simp only [mul_inv_cancel₀ hae,unitPower_one]

/-- A positive common-shock parameter puts positive mass on the diagonal. -/
theorem cuadrasAuge_diagonal_ne_zero (δ : I) (hδ : 0<δ) :
    (cuadrasAuge δ).toMeasure {x | x 0=x 1}≠0 := by
  let t := unitPower unitHalf δ δ.property.1
  let s := unitPower unitHalf (unitInterval.symm δ) (unitInterval.symm δ).property.1
  let A : Set (Fin 2 → I) := {x | x 0=x 1 ∧ t≤x 0}
  let B : Set (Fin 2 → I) := Iic ![s,s]
  let S : Set (Fin 2 → I) := {x | x 0=x 1}
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)).inter
      (measurableSet_le measurable_const (measurable_subtype_coe.comp (measurable_pi_apply 0)))
  have hS : MeasurableSet S := measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)
  have ht : (t:ℝ)<1 :=
    Real.rpow_lt_one (by norm_num [unitHalf]) (by norm_num [unitHalf]) (show (0:ℝ)<δ from hδ)
  have hs : 0<(s:ℝ) := Real.rpow_pos_of_pos (by norm_num [unitHalf]) _
  have hmA : (comonotonic 2).toMeasure A≠0 := by
    rw [toMeasure_comonotonic,Measure.map_apply (by fun_prop) hA]
    have he : (fun u : I => fun _ : Fin 2 => u) ⁻¹' A=Ici t := by ext u; simp [A]
    rw [he,unitInterval.volume_Ici]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)).ne'
  have hmB : (independence 2).toMeasure B≠0 := by
    have hh : 0<(independence 2).cdf ![s,s] := by
      simp only [cdf_independence,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      positivity
    intro hz
    change 0<((independence 2).toMeasure B).toReal at hh
    rw [hz] at hh
    simp at hh
  have hsub : A ×ˢ B ⊆ maxProductPoint ![δ,δ] ⁻¹' S := by
    intro p hp
    have hcommon : unitHalf≤powerSample δ (p.1 0) := by
      rw [← powerSample_unitPower δ hδ unitHalf]
      exact powerSample_mono δ hp.1.2
    have hn (i : Fin 2) : powerSample (unitInterval.symm δ) (p.2 i)≤unitHalf := by
      apply (powerSample_le_iff _ _ _).mpr
      have hh := hp.2 i
      fin_cases i <;> exact hh
    change max (powerSample δ (p.1 0)) (powerSample (unitInterval.symm δ) (p.2 0)) =
      max (powerSample δ (p.1 1)) (powerSample (unitInterval.symm δ) (p.2 1))
    rw [max_eq_left ((hn 0).trans hcommon),← hp.1.1,
      max_eq_left ((hn 1).trans hcommon)]
  intro hz
  have hm : ((comonotonic 2).toMeasure.prod (independence 2).toMeasure)
      (maxProductPoint ![δ,δ] ⁻¹' S)=0 := by
    change (((comonotonic 2).toMeasure.prod (independence 2).toMeasure).map (maxProductPoint ![δ,δ])) S=0 at hz
    rwa [Measure.map_apply (measurable_maxProductPoint _) hS] at hz
  have hzero := measure_mono (μ := (comonotonic 2).toMeasure.prod (independence 2).toMeasure) hsub
  rw [hm,Measure.prod_prod] at hzero
  exact (mul_ne_zero hmA hmB) (le_antisymm hzero bot_le)

theorem cuadrasAuge_absolutelyContinuous_iff (δ : I) :
    (cuadrasAuge δ).toMeasure ≪ (volume : Measure (Fin 2 → I)) ↔ δ=0 := by
  constructor
  · intro h
    by_contra hδ
    exact cuadrasAuge_diagonal_ne_zero δ (lt_of_le_of_ne δ.property.1 (Ne.symm hδ)) (h volume_cube_diagonal)
  · rintro rfl
    simp only [cuadrasAuge,marshallOlkin_zero_zero]
    exact Measure.AbsolutelyContinuous.rfl

theorem cuadrasAuge_density_tp2_iff (δ : I) : (cuadrasAuge δ).HasMTP2Density ↔ δ=0 := by
  constructor
  · exact fun h => (cuadrasAuge_absolutelyContinuous_iff δ).mp h.absolutelyContinuous
  · rintro rfl
    simpa only [cuadrasAuge,marshallOlkin_zero_zero] using hasMTP2Density_independence 2

end Verification
