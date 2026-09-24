import Papers.Rockel2026ExactBlest.ExactBlestConstructions
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! The conditional branches of the randomized extremizer. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology ENNReal
open ProbabilityTheory.Copula.OrdinalSum
namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

def blockLow (a u : I) : Fin 2 → I := ![lowerEmbed a u, unitInterval.symm (lowerEmbed a u)]
def blockPlus (a p u : I) : Fin 2 → I :=
  ![upperEmbed a u, unitInterval.symm (upperEmbed a (lowerEmbed p u))]
def blockMinus (a p u : I) : Fin 2 → I :=
  ![upperEmbed a u, unitInterval.symm (upperEmbed a (upperEmbed p (unitInterval.symm u)))]

theorem continuous_blockLow (a : I) : Continuous (blockLow a) := by unfold blockLow; fun_prop
theorem continuous_blockPlus (a p : I) : Continuous (blockPlus a p) := by unfold blockPlus; fun_prop
theorem continuous_blockMinus (a p : I) : Continuous (blockMinus a p) := by unfold blockMinus; fun_prop
attribute [fun_prop] continuous_blockLow continuous_blockPlus continuous_blockMinus

theorem block_joint_law (a p : I) :
    (((Copula.comonotonic 2).ordinalSum (skewTent p) a).reflect {1}).toMeasure =
      ENNReal.ofReal (a : ℝ) • (volume : Measure I).map (blockLow a) +
      ENNReal.ofReal (1 - (a : ℝ)) •
        (ENNReal.ofReal (p : ℝ) • (volume : Measure I).map (blockPlus a p) +
          ENNReal.ofReal (1 - (p : ℝ)) • (volume : Measure I).map (blockMinus a p)) := by
  let L := fun x : Fin 2 → I => fun i => lowerEmbed a (x i)
  let U := fun x : Fin 2 → I => fun i => upperEmbed a (x i)
  let R := Copula.reflectPoint ({1} : Finset (Fin 2))
  have hL : Measurable L := by dsimp [L]; fun_prop
  have hU : Measurable U := by dsimp [U]; fun_prop
  have hR : Measurable R := Copula.measurable_reflectPoint _
  rw [Copula.toMeasure_reflect, Copula.toMeasure_ordinalSum,
    Measure.map_add _ _ hR, Measure.map_smul _ hR.aemeasurable,
    Measure.map_smul _ hR.aemeasurable]
  congr 1
  · rw [Copula.toMeasure_comonotonic, Measure.map_map hL (by fun_prop),
      Measure.map_map hR (hL.comp (by fun_prop))]
    congr 2
    ext u i
    fin_cases i <;> simp [Function.comp_def, L, R, blockLow, Copula.reflectPoint]
  · change ENNReal.ofReal (1 - (a : ℝ)) • (((stripMeasure (Copula.comonotonic 2)
      Copula.countermonotonic p).map U).map R) = _
    congr 1
    rw [stripMeasure, Measure.map_add _ _ hU, Measure.map_smul _ hU.aemeasurable,
      Measure.map_smul _ hU.aemeasurable, Measure.map_add _ _ hR,
      Measure.map_smul _ hR.aemeasurable, Measure.map_smul _ hR.aemeasurable,
      Copula.toMeasure_comonotonic, Copula.toMeasure_countermonotonic]
    congr 1
    · rw [Measure.map_map (continuous_stripLower p).measurable (by fun_prop),
        Measure.map_map hU (by fun_prop), Measure.map_map hR (by fun_prop)]
      congr 2
      ext u i
      fin_cases i <;> simp [Function.comp_def, U, R, blockPlus, stripLower, Copula.reflectPoint]
    · rw [Measure.map_map (continuous_stripUpper p).measurable (by fun_prop),
        Measure.map_map hU (by fun_prop), Measure.map_map hR (by fun_prop)]
      congr 2
      ext u i
      fin_cases i <;> simp [Function.comp_def, U, R, blockMinus, stripUpper, Copula.reflectPoint]

theorem familyB_joint_law (a : I) (ha : 1 / 2 ≤ (a : ℝ)) :
    (familyB a ha).survivalCopula.toMeasure =
      ENNReal.ofReal (a : ℝ) • (volume : Measure I).map (blockLow a) +
      ENNReal.ofReal (1 - (a : ℝ)) •
        (ENNReal.ofReal (randomSplit a ha : ℝ) • (volume : Measure I).map (blockPlus a (randomSplit a ha)) +
          ENNReal.ofReal (1 - (randomSplit a ha : ℝ)) • (volume : Measure I).map (blockMinus a (randomSplit a ha))) := by
  unfold familyB
  rw [← Copula.reflect_first_second, Copula.reflect_reflect]
  exact block_joint_law a (randomSplit a ha)

theorem block_branches_formula (a : I) (ha : 1 / 2 ≤ (a : ℝ)) (u : I) :
    (blockMinus a (randomSplit a ha) u 1 : ℝ) = ((upperEmbed a u : ℝ) - a) / (2 * a) ∧
    (blockPlus a (randomSplit a ha) u 1 : ℝ) =
      ((a : ℝ) + (upperEmbed a u : ℝ) - 2 * a * (upperEmbed a u : ℝ)) / (2 * a) ∧
    1 - (randomSplit a ha : ℝ) = 1 / (2 * a) := by
  have ha0 : (a : ℝ) ≠ 0 := by linarith
  simp only [blockMinus, blockPlus, Matrix.cons_val_one, Matrix.cons_val_zero, upperEmbed, lowerEmbed,
    unitInterval.coe_symm_eq, randomSplit]
  constructor
  · field_simp; ring
  constructor <;> (field_simp; ring)

theorem measurable_weighted_dirac (c : ℝ≥0∞) (f : I → I) (hf : Measurable f) :
    Measurable (fun x => c • Measure.dirac (f x)) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  exact measurable_const.mul ((Measure.measurable_coe hs).comp (Measure.measurable_dirac.comp hf))

def blockKernel (a p : I) : Kernel I I where
  toFun x := if x ≤ a then Measure.dirac (unitInterval.symm x) else
    ENNReal.ofReal (p : ℝ) • Measure.dirac (unitInterval.symm (upperEmbed a (lowerEmbed p (upperCoord a x)))) +
    ENNReal.ofReal (1 - (p : ℝ)) • Measure.dirac (unitInterval.symm (upperEmbed a (upperEmbed p (unitInterval.symm (upperCoord a x)))))
  measurable' := by
    have huc : Measurable (upperCoord a) := (continuous_upperCoord a).measurable
    apply Measurable.ite measurableSet_Iic
    · fun_prop
    · apply Measurable.add
      · exact measurable_weighted_dirac _ _ (by fun_prop)
      · exact measurable_weighted_dirac _ _ (by fun_prop)

instance blockKernel_markov (a p : I) : IsMarkovKernel (blockKernel a p) := by
  constructor
  intro x
  constructor
  dsimp only [blockKernel, Kernel.coe_mk]
  split_ifs
  · simp
  · simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add p.property.1 (sub_nonneg.mpr p.property.2)]
    simp

theorem block_disintegration (a p : I) (ha : (a : ℝ) < 1)
    (f : (Fin 2 → I) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂(((Copula.comonotonic 2).ordinalSum (skewTent p) a).reflect {1}).toMeasure) =
      ∫⁻ x : I, ∫⁻ z, f ![x, z] ∂blockKernel a p x := by
  let g := fun x : I => ∫⁻ z, f ![x, z] ∂blockKernel a p x
  have hg : Measurable g :=
    (show Measurable (fun x : I × I => f ![x.1, x.2]) by fun_prop).lintegral_kernel_prod_right'
  have hl : (fun u : I => g (lowerEmbed a u)) = fun u => f (blockLow a u) := by
    funext u
    simp [g, blockKernel, lowerEmbed_le, blockLow]
  have hu0 : ∀ᵐ u : I, u ≠ 0 := by simp [ae_iff]
  have hu : (fun u : I => g (upperEmbed a u)) =ᵐ[volume]
      (fun u => ENNReal.ofReal (p : ℝ) * f (blockPlus a p u) +
        ENNReal.ofReal (1 - (p : ℝ)) * f (blockMinus a p u)) := by
    filter_upwards [hu0] with u hu
    have hu1 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
    have hcut : ¬upperEmbed a u ≤ a := by
      change ¬(a : ℝ) + (1 - (a : ℝ)) * u ≤ a
      nlinarith
    simp [g, blockKernel, hcut, lintegral_add_measure, lintegral_smul_measure,
      upperCoord_upperEmbed a u ha, blockPlus, blockMinus]
  have hs : (∫⁻ x : I, g x) = ENNReal.ofReal (a : ℝ) * (∫⁻ u : I, g (lowerEmbed a u)) +
      ENNReal.ofReal (1 - (a : ℝ)) * (∫⁻ u : I, g (upperEmbed a u)) := by
    calc
      _ = ∫⁻ x, g x ∂(ENNReal.ofReal (a : ℝ) • (volume : Measure I).map (lowerEmbed a) +
          ENNReal.ofReal (1 - (a : ℝ)) • (volume : Measure I).map (upperEmbed a)) := by rw [uniform_split]
      _ = _ := by rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
        lintegral_map hg (by fun_prop), lintegral_map hg (by fun_prop)]; simp only [smul_eq_mul]
  change _ = ∫⁻ x : I, g x
  rw [hs, hl, lintegral_congr_ae hu, lintegral_add_left (by fun_prop),
    lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
    block_joint_law, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_map hf (by fun_prop), lintegral_map hf (by fun_prop), lintegral_map hf (by fun_prop)]
  simp only [smul_eq_mul]

theorem familyB_disintegration (a : I) (ha : 1 / 2 ≤ (a : ℝ)) (ha1 : (a : ℝ) < 1)
    (f : (Fin 2 → I) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂(familyB a ha).survivalCopula.toMeasure) =
      ∫⁻ x : I, ∫⁻ z, f ![x, z] ∂blockKernel a (randomSplit a ha) x := by
  unfold familyB
  rw [← Copula.reflect_first_second, Copula.reflect_reflect]
  exact block_disintegration a (randomSplit a ha) ha1 f hf

theorem block_not_first_graph (a p : I) (ha : (a : ℝ) < 1)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (f : I → I) (hf : Measurable f) :
    ¬(∀ᵐ x ∂(((Copula.comonotonic 2).ordinalSum (skewTent p) a).reflect {1}).toMeasure,
      x 1 = f (x 0)) := by
  intro h
  rw [block_joint_law, ae_add_measure_iff] at h
  have hu := (Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (1 - (a : ℝ)) ≠ 0)).mp h.2
  rw [ae_add_measure_iff] at hu
  have hp := (Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (p : ℝ) ≠ 0)).mp hu.1
  have hm := (Measure.ae_ennreal_smul_measure_iff (by positivity : ENNReal.ofReal (1 - (p : ℝ)) ≠ 0)).mp hu.2
  have hs : MeasurableSet {x : Fin 2 → I | x 1 = f (x 0)} :=
    measurableSet_eq_fun (measurable_pi_apply 1) (hf.comp (measurable_pi_apply 0))
  have hpa := (ae_map_iff (continuous_blockPlus a p).measurable.aemeasurable hs).mp hp
  have hma := (ae_map_iff (continuous_blockMinus a p).measurable.aemeasurable hs).mp hm
  have hn : ∀ᵐ u : I, u ≠ 1 := by simp [ae_iff]
  have hfalse : ∀ᵐ u : I, False := by
    filter_upwards [hpa, hma, hn] with u hpu hmu hnu
    have he : blockPlus a p u 1 = blockMinus a p u 1 := hpu.trans hmu.symm
    have hr := congrArg (fun z : I => (z : ℝ)) he
    simp only [blockPlus, blockMinus, Matrix.cons_val_one, Matrix.cons_val_zero,
      unitInterval.coe_symm_eq, upperEmbed, lowerEmbed] at hr
    have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (fun he => hnu (Subtype.ext he))
    have hpos : 0 < (1 - (a : ℝ)) * (1 - (u : ℝ)) := by positivity
    nlinarith
  have hz : (volume : Measure I) univ = 0 := by simpa using (ae_iff.mp hfalse)
  simp at hz

theorem familyB_not_first_graph (a : I) (ha : 1 / 2 < (a : ℝ)) (ha1 : (a : ℝ) < 1)
    (f : I → I) (hf : Measurable f) :
    ¬(∀ᵐ x ∂(familyB a ha.le).survivalCopula.toMeasure, x 1 = f (x 0)) := by
  unfold familyB
  rw [← Copula.reflect_first_second, Copula.reflect_reflect]
  apply block_not_first_graph a (randomSplit a ha.le) ha1 ?_ ?_ f hf
  · change 0 < (2 * (a : ℝ) - 1) / (2 * a)
    exact div_pos (by linarith) (by linarith)
  · change (2 * (a : ℝ) - 1) / (2 * a) < 1
    rw [div_lt_one (by linarith : 0 < 2 * (a : ℝ))]
    linarith

theorem upperEmbed_upperCoord (a x : I) (ha : (a : ℝ) < 1) (hx : a ≤ x) :
    upperEmbed a (upperCoord a x) = x := by
  apply Subtype.ext
  change (a : ℝ) + (1 - (a : ℝ)) * (upperCoord a x : ℝ) = x
  rw [coe_upperCoord_of_ge a x ha hx]
  have hd : 1 - (a : ℝ) ≠ 0 := by linarith
  field_simp
  ring

theorem familyB_conditional_formula (a : I) (ha : 1 / 2 ≤ (a : ℝ)) (ha1 : (a : ℝ) < 1)
    (x : I) :
    (blockKernel a (randomSplit a ha) x).map (fun z : I => (z : ℝ)) =
      if x ≤ a then Measure.dirac (1 - (x : ℝ)) else
        ENNReal.ofReal (1 / (2 * (a : ℝ))) • Measure.dirac (((x : ℝ) - a) / (2 * a)) +
        ENNReal.ofReal ((2 * (a : ℝ) - 1) / (2 * a)) •
          Measure.dirac (((a : ℝ) + x - 2 * a * x) / (2 * a)) := by
  by_cases hx : x ≤ a
  · simp [blockKernel, hx, Measure.map_dirac, unitInterval.coe_symm_eq]
  · have hi := upperEmbed_upperCoord a x ha1 (le_of_not_ge hx)
    have hb := block_branches_formula a ha (upperCoord a x)
    rw [hi] at hb
    have hm : (unitInterval.symm (upperEmbed a (upperEmbed (randomSplit a ha)
        (unitInterval.symm (upperCoord a x)))) : ℝ) = ((x : ℝ) - a) / (2 * a) := hb.1
    have hp : (unitInterval.symm (upperEmbed a (lowerEmbed (randomSplit a ha)
        (upperCoord a x))) : ℝ) = ((a : ℝ) + x - 2 * a * x) / (2 * a) := hb.2.1
    simp only [blockKernel, Kernel.coe_mk, ite_eq_right hx,
      Measure.map_add _ _ measurable_subtype_coe,
      Measure.map_smul _ measurable_subtype_coe.aemeasurable, Measure.map_dirac, hm, hp, hb.2.2]
    change ENNReal.ofReal ((2 * (a : ℝ) - 1) / (2 * a)) • _ + _ = _
    exact add_comm _ _

theorem randomized_optimizer_not_first_graph (C : Copula 2) (a : I)
    (ha : 1 / 2 < (a : ℝ)) (ha1 : (a : ℝ) < 1)
    (he : eta C = etaB a) (hn : Papers.Rockel2026XiBlest.blestNu C = nuB a)
    (f : I → I) (hf : Measurable f) :
    ¬(∀ᵐ x ∂C.survivalCopula.toMeasure, x 1 = f (x 0)) := by
  rw [randomized_upper_unique C a ha ha1 he hn]
  exact familyB_not_first_graph a ha ha1 f hf

#assert_standard_axioms Papers.Rockel2026ExactBlest.upperEmbed_upperCoord
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_weighted_dirac
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyB_conditional_formula
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_optimizer_not_first_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.blockKernel_markov
#assert_standard_axioms Papers.Rockel2026ExactBlest.block_not_first_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyB_not_first_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.block_disintegration
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyB_disintegration
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_blockLow
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_blockPlus
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_blockMinus
#assert_standard_axioms Papers.Rockel2026ExactBlest.block_joint_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyB_joint_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.block_branches_formula
end
end Papers.Rockel2026ExactBlest
