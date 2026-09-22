import Verification.FoldedUniform

/-! # Identifying the folded example with its stated joint law -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def foldSample (p : I × I) : Fin 2 → I :=
  if (p.2 : ℝ) ≤ 1/2 then ![p.1,foldLower p.1] else ![p.1,foldUpper p.1]

theorem foldSample_measurable : Measurable foldSample := by
  unfold foldSample
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

private theorem integral_half_choice (a b : ℝ) :
    (∫ z : I, if (z : ℝ) ≤ 1/2 then a else b) = (a+b)/2 := by
  have he (z : I) : (if (z : ℝ) ≤ 1/2 then a else b) =
      b+(a-b)*(if (z : ℝ) ≤ 1/2 then (1 : ℝ) else 0) := by split_ifs <;> ring
  simp_rw [he]
  have hi : Integrable (fun z : I => if (z : ℝ) ≤ 1/2 then (1 : ℝ) else 0) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.ite (measurableSet_le measurable_subtype_coe measurable_const) measurable_const).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun z => by split_ifs <;> norm_num
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul, integral_unit_le_real]
  norm_num [unitClamp]
  ring

theorem foldSample_orthant (u v : I) :
    (∫ p : I × I, if foldSample p ≤ ![u,v] then (1 : ℝ) else 0) = foldedUniform.cdf ![u,v] := by
  have hi : Integrable (fun p : I × I => if foldSample p ≤ ![u,v] then (1 : ℝ) else 0) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.ite (measurableSet_le foldSample_measurable measurable_const) measurable_const).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun p => by split_ifs <;> norm_num
  change (∫ p : I × I, if foldSample p ≤ ![u,v] then (1 : ℝ) else 0 ∂(volume : Measure I).prod volume) = _
  rw [integral_prod _ hi]
  have he (t : I) : (∫ z : I, if foldSample (t,z) ≤ ![u,v] then (1 : ℝ) else 0) =
      (Iic u).indicator (foldKernel v) t := by
    have hp (z : I) : (if foldSample (t,z) ≤ ![u,v] then (1 : ℝ) else 0) =
        if (z : ℝ) ≤ 1/2 then (if t ≤ u ∧ foldLower t ≤ v then 1 else 0)
        else (if t ≤ u ∧ foldUpper t ≤ v then 1 else 0) := by
      by_cases hz : (z : ℝ) ≤ 1/2 <;>
        simp only [foldSample,hz,ite_true,ite_false,Pi.le_def,Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    simp_rw [hp]
    rw [integral_half_choice]
    by_cases ht : t ≤ u
    · rw [indicator_of_mem (show t ∈ Iic u from ht)]
      simp only [ht, true_and, foldKernel]
      ring
    · rw [indicator_of_notMem (show t ∉ Iic u from ht)]
      simp [ht]
  simp_rw [he]
  rw [integral_indicator measurableSet_Iic]
  exact (foldedUniform_cdf u v).symm

theorem foldedUniform_toMeasure_sample :
    foldedUniform.toMeasure = (volume : Measure (I × I)).map foldSample := by
  let μ : ProbabilityMeasure (Fin 2 → I) :=
    ProbabilityMeasure.map (⟨volume,inferInstance⟩ : ProbabilityMeasure (I × I)) foldSample
  have hμ (u : Fin 2 → I) : μ.toMeasure.real (Iic u) = foldedUniform.cdf u := by
    change ((volume : Measure (I × I)).map foldSample).real (Iic u) = _
    rw [map_measureReal_apply foldSample_measurable measurableSet_Iic]
    have he : ![u 0,u 1] = u := by ext i; fin_cases i <;> rfl
    have hi := integral_indicator (μ := (volume : Measure (I × I)))
      (f := fun _ => (1 : ℝ)) (s := foldSample ⁻¹' Iic u) (foldSample_measurable measurableSet_Iic)
    have hf : volume.real (foldSample ⁻¹' Iic u) =
        ∫ p : I × I, if foldSample p ≤ u then (1 : ℝ) else 0 := by
      simpa [Set.indicator,smul_eq_mul] using hi.symm
    rw [hf,← he]
    exact foldSample_orthant _ _
  let D := foldedUniform.isClassical_cdf.ofMeasure μ hμ
  have he : D = foldedUniform := Copula.cdf_injective (foldedUniform.isClassical_cdf.cdf_ofMeasure μ hμ)
  rw [← he]
  rfl

noncomputable def foldRank (u : I) : I :=
  ⟨|2*(u : ℝ)-1|, abs_nonneg _, abs_le.mpr ⟨by linarith [u.property.1],by linarith [u.property.2]⟩⟩

@[fun_prop] theorem continuous_foldRank : Continuous foldRank := by unfold foldRank; fun_prop

private theorem foldSample_graph (p : I × I) :
    ![foldRank (foldSample p 1),foldSample p 1] = foldSample p := by
  unfold foldSample
  split_ifs
  · ext i
    fin_cases i
    · change |2*((1-(p.1 : ℝ))/2)-1| = (p.1 : ℝ)
      rw [show 2*((1-(p.1 : ℝ))/2)-1 = -(p.1 : ℝ) by ring, abs_neg, abs_of_nonneg p.1.property.1]
    · rfl
  · ext i
    fin_cases i
    · change |2*((1+(p.1 : ℝ))/2)-1| = (p.1 : ℝ)
      rw [show 2*((1+(p.1 : ℝ))/2)-1 = (p.1 : ℝ) by ring, abs_of_nonneg p.1.property.1]
    · rfl

/-- Exactly the law of (abs(2U-1), U), with U uniform. -/
theorem foldedUniform_joint_law :
    foldedUniform.toMeasure = (volume : Measure I).map (fun u => ![foldRank u,u]) := by
  have hg : foldedUniform.toMeasure = foldedUniform.toMeasure.map (fun x => ![foldRank (x 1),x 1]) := by
    rw [foldedUniform_toMeasure_sample, Measure.map_map (by fun_prop) foldSample_measurable]
    congr 1
    funext p
    exact (foldSample_graph p).symm
  calc
    _ = foldedUniform.toMeasure.map (fun x => ![foldRank (x 1),x 1]) := hg
    _ = (foldedUniform.toMeasure.map (fun x => x 1)).map (fun u => ![foldRank u,u]) :=
      (Measure.map_map (show Measurable (fun u : I => ![foldRank u,u]) by fun_prop) (measurable_pi_apply 1)).symm
    _ = _ := by rw [foldedUniform.map_eval]

/-- The first variable in the source example is uniform too. -/
theorem foldRank_measurePreserving : MeasurePreserving foldRank (volume : Measure I) volume := by
  refine ⟨continuous_foldRank.measurable,?_⟩
  have h := foldedUniform.map_eval 0
  rw [foldedUniform_joint_law, Measure.map_map (measurable_pi_apply 0) (by fun_prop)] at h
  exact h

end Verification
