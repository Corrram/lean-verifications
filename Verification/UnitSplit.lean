import Copula.OrdinalSum.Measure

/-! # Splitting a uniform predictor into two affine blocks -/

open MeasureTheory ProbabilityTheory Set Copula.OrdinalSum
open scoped unitInterval

namespace Verification

theorem volume_unit_split (a : I) :
    (volume : Measure I) = ENNReal.ofReal (a : ℝ) • volume.map (lowerEmbed a) +
      ENNReal.ofReal (1-(a : ℝ)) • volume.map (upperEmbed a) := by
  let C := Copula.comonotonic 2
  have h := congrArg (fun μ : Measure (Fin 2 → I) => μ.map (fun x => x 0))
    (Copula.toMeasure_ordinalSum C C a)
  rw [Copula.map_eval,Measure.map_add _ _ (measurable_pi_apply 0),
    Measure.map_smul _ (measurable_pi_apply 0).aemeasurable,
    Measure.map_smul _ (measurable_pi_apply 0).aemeasurable,
    Measure.map_map (measurable_pi_apply 0) (by fun_prop),
    Measure.map_map (measurable_pi_apply 0) (by fun_prop)] at h
  change volume = ENNReal.ofReal (a : ℝ) • C.toMeasure.map (lowerEmbed a ∘ (fun x => x 0)) +
    ENNReal.ofReal (1-(a : ℝ)) • C.toMeasure.map (upperEmbed a ∘ (fun x => x 0)) at h
  rw [← Measure.map_map (measurable_lowerEmbed _) (measurable_pi_apply 0),
    ← Measure.map_map (measurable_upperEmbed _) (measurable_pi_apply 0),C.map_eval] at h
  exact h

theorem integral_unit_split (a : I) (f : I → ℝ) (hf : Measurable f)
    (hL : Integrable (fun u => f (lowerEmbed a u)))
    (hU : Integrable (fun u => f (upperEmbed a u))) :
    (∫ u : I, f u) = (a : ℝ)*(∫ u : I, f (lowerEmbed a u))+
      (1-(a : ℝ))*(∫ u : I, f (upperEmbed a u)) := by
  have hiL := (integrable_map_measure hf.aestronglyMeasurable (measurable_lowerEmbed a).aemeasurable).mpr hL
  have hiU := (integrable_map_measure hf.aestronglyMeasurable (measurable_upperEmbed a).aemeasurable).mpr hU
  conv_lhs => rw [volume_unit_split a]
  rw [integral_add_measure (hiL.smul_measure ENNReal.ofReal_ne_top) (hiU.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure,integral_smul_measure,
    integral_map (measurable_lowerEmbed a).aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_upperEmbed a).aemeasurable hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal a.property.1,ENNReal.toReal_ofReal (sub_nonneg.mpr a.property.2)]
  rfl

noncomputable def unitJoin (a : I) (f g : I → ℝ) (u : I) : ℝ :=
  if u ≤ a then f (lowerCoord a u) else g (upperCoord a u)

theorem measurable_unitJoin (a : I) {f g : I → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (unitJoin a f g) :=
  (hf.comp (continuous_lowerCoord a).measurable).ite measurableSet_Iic
    (hg.comp (continuous_upperCoord a).measurable)

theorem unitJoin_lower (a : I) (ha : 0 < a) (f g : I → ℝ) (u : I) :
    unitJoin a f g (lowerEmbed a u) = f u := by
  rw [unitJoin,ite_eq_left (lowerEmbed_le a u),lowerCoord_lowerEmbed a u ha]

theorem unitJoin_upper (a : I) (ha : a < 1) (f g : I → ℝ) :
    (fun u => unitJoin a f g (upperEmbed a u)) =ᵐ[volume] g := by
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with u hu
  have hp : (0 : ℝ) < u := lt_of_le_of_ne u.property.1 (Ne.symm (by intro hz; exact hu (Subtype.ext hz)))
  have hn : ¬ upperEmbed a u ≤ a := by
    change ¬ (a : ℝ)+(1-(a : ℝ))*(u : ℝ) ≤ a
    nlinarith [mul_pos (sub_pos.mpr (show (a : ℝ) < 1 from ha)) hp]
  rw [unitJoin,ite_eq_right hn,upperCoord_upperEmbed a u ha]

theorem integral_unitJoin (a : I) (ha0 : 0 < a) (ha1 : a < 1)
    (f g : I → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable f) (hj : Integrable g) :
    (∫ u : I, unitJoin a f g u) = (a : ℝ)*(∫ u : I, f u)+(1-(a : ℝ))*(∫ u : I, g u) := by
  have hL : (fun u => unitJoin a f g (lowerEmbed a u)) = f := funext (unitJoin_lower a ha0 f g)
  have hU := unitJoin_upper a ha1 f g
  rw [integral_unit_split a _ (measurable_unitJoin a hf hg)
    (by rw [hL]; exact hi) (hj.congr hU.symm),hL,integral_congr_ae hU]

theorem integral_lowerCoord (a : I) (ha : 0 < a) (f : I → ℝ)
    (hf : Measurable f) (hi : Integrable f) :
    (∫ u : I, f (lowerCoord a u)) = (a : ℝ)*(∫ u : I, f u)+(1-(a : ℝ))*f 1 := by
  have hL : (fun u => f (lowerCoord a (lowerEmbed a u))) = f := by
    funext u; rw [lowerCoord_lowerEmbed a u ha]
  have hU : (fun u => f (lowerCoord a (upperEmbed a u))) = fun _ => f 1 := by
    funext u; rw [lowerCoord_of_ge a _ ha (le_upperEmbed a u)]
  rw [integral_unit_split a (fun u => f (lowerCoord a u)) (hf.comp (continuous_lowerCoord a).measurable)
    (by rw [hL]; exact hi) (by rw [hU]; exact integrable_const _),hL,hU]
  simp

theorem integral_upperCoord (a : I) (ha : a < 1) (f : I → ℝ)
    (hf : Measurable f) (hi : Integrable f) :
    (∫ u : I, f (upperCoord a u)) = (a : ℝ)*f 0+(1-(a : ℝ))*(∫ u : I, f u) := by
  have hL : (fun u => f (upperCoord a (lowerEmbed a u))) = fun _ => f 0 := by
    funext u; rw [upperCoord_of_le a _ (lowerEmbed_le a u)]
  have hU : (fun u => f (upperCoord a (upperEmbed a u))) = f := by
    funext u; rw [upperCoord_upperEmbed a u ha]
  rw [integral_unit_split a (fun u => f (upperCoord a u)) (hf.comp (continuous_upperCoord a).measurable)
    (by rw [hL]; exact integrable_const _) (by rw [hU]; exact hi),hL,hU]
  simp

end Verification
