import Papers.Rockel2026ExactBlest.ExactBlestPotentials

/-! Direct graph-law identifications, including parameters outside the boundary regime. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology
open ProbabilityTheory.Copula.OrdinalSum
namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

theorem familyA_survival (w : I) :
    (familyA w).survivalCopula =
      ((Copula.comonotonic 2).ordinalSum Copula.countermonotonic w).reflect {1} := by
  unfold familyA
  rw [← Copula.reflect_first_second, Copula.reflect_reflect]

theorem familyA_graph_all (w : I) :
    ∀ᵐ x ∂(familyA w).survivalCopula.toMeasure, x 1 = graphRank w (x 0) := by
  have hg := measurable_graphRank w
  have hp : MeasurableSet {x : Fin 2 → I | x 1 = graphRank w (x 0)} :=
    measurableSet_eq_fun (measurable_pi_apply 1) (hg.comp (measurable_pi_apply 0))
  rw [familyA_survival, Copula.toMeasure_reflect]
  apply (ae_map_iff (Copula.measurable_reflectPoint _).aemeasurable hp).mpr
  have hp' : MeasurableSet {x : Fin 2 → I |
      Copula.reflectPoint {1} x 1 = graphRank w (Copula.reflectPoint {1} x 0)} := by
    exact Copula.measurable_reflectPoint _ hp
  rw [Copula.toMeasure_ordinalSum, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    have hm : Measurable (fun x : Fin 2 → I => fun i => lowerEmbed w (x i)) := by
      unfold lowerEmbed; fun_prop
    apply (ae_map_iff hm.aemeasurable hp').mpr
    rw [Copula.toMeasure_comonotonic]
    apply (ae_map_iff (by fun_prop) (hm hp')).mpr
    filter_upwards [] with u
    apply Subtype.ext
    have hl : (lowerEmbed w u : ℝ) ≤ w := lowerEmbed_le w u
    simp [Copula.reflectPoint, graphRank, hl]
  · apply Measure.ae_smul_measure
    have hm : Measurable (fun x : Fin 2 → I => fun i => upperEmbed w (x i)) := by
      unfold upperEmbed; fun_prop
    apply (ae_map_iff hm.aemeasurable hp').mpr
    rw [Copula.toMeasure_countermonotonic]
    apply (ae_map_iff (by fun_prop) (hm hp')).mpr
    have hu0 : ∀ᵐ u : I, u ≠ 0 := by simp [ae_iff]
    filter_upwards [hu0] with u hu
    apply Subtype.ext
    by_cases hw : w = 1
    · subst w
      simp [Copula.reflectPoint, graphRank, upperEmbed]
    · have hw1 : (w : ℝ) < 1 := lt_of_le_of_ne w.property.2 (fun h => hw (Subtype.ext h))
      have hu1 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
      have hl : ¬(upperEmbed w u : ℝ) ≤ w := by
        change ¬(w : ℝ) + (1 - (w : ℝ)) * u ≤ w
        nlinarith
      change 1 - (upperEmbed w (unitInterval.symm u) : ℝ) =
        if (upperEmbed w u : ℝ) ≤ w then 1 - (upperEmbed w u : ℝ) else (upperEmbed w u : ℝ) - w
      rw [ite_eq_right hl]
      simp only [upperEmbed, unitInterval.coe_symm_eq]
      ring

theorem familyA_graph_law_all (w : I) :
    (familyA w).survivalCopula.toMeasure = (volume : Measure I).map (fun u => ![u, graphRank w u]) := by
  let E := (familyA w).survivalCopula
  have hm : Measurable (fun u : I => ![u, graphRank w u]) := by
    have := measurable_graphRank w
    fun_prop
  rw [← E.map_eval 0, Measure.map_map hm (measurable_pi_apply 0)]
  have hv : (fun x : Fin 2 → I => ![x 0, graphRank w (x 0)]) =ᵐ[E.toMeasure] id := by
    filter_upwards [familyA_graph_all w] with x hx
    funext i
    fin_cases i
    · rfl
    · exact hx.symm
  change E.toMeasure = E.toMeasure.map (fun x => ![x 0, graphRank w (x 0)])
  rw [Measure.map_congr hv, Measure.map_id]

#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_survival
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_graph_all
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_graph_law_all
end
end Papers.Rockel2026ExactBlest
