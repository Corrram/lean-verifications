import Papers.OrendayLaresRockel2026XiBeta.RBranchLaw

/-! # `R_b` is the copula of `(U, V_b)` and is singular (Proposition 5.3 (i))

The support of `R_b` is a finite union of line segments (three graphs of affine maps), a Lebesgue
null set carrying all the mass; hence `R_b` is singular and has no density.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval ENNReal

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The underlying probability space `I × Bool` (uniform `U` and independent fair coin `ε`). -/
noncomputable def probVb : ProbabilityMeasure (I × Bool) :=
  ⟨volume.prod bernoulliHalf, inferInstance⟩

theorem marginals_Xb {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (i : Fin 2) :
    probVb.toMeasure.map (fun ω => Xb b ω i) = volume := by
  have h := (Rb b hb).map_eval i
  rw [Rb_toMeasure_eq_lawVb hb, lawVb, Measure.map_map (measurable_pi_apply i) (measurable_Xb b)] at h
  exact h

/-- **Proposition 5.3, first statement**: `R_b` is the copula of the random vector `(U, V_b)`. -/
theorem Rb_eq_ofMap {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    Rb b hb = Copula.ofMap probVb (Xb b) (measurable_Xb b) (marginals_Xb hb) := by
  apply Copula.ext
  rw [Copula.toMeasure_ofMap, Rb_toMeasure_eq_lawVb hb]
  rfl

/-- `V_b` is uniformly distributed on `[0,1]`. -/
theorem Vb_uniform {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    probVb.toMeasure.map (fun ω => Vb b ω.1 ω.2) = volume :=
  marginals_Xb hb 1

theorem volume_graph_null (f : I → ℝ) (hf : Measurable f) :
    (volume : Measure (Fin 2 → I)) {x | (x 1 : ℝ) = f (x 0)} = 0 := by
  have hs : MeasurableSet {p : I × I | (p.2 : ℝ) = f p.1} :=
    measurableSet_eq_fun (measurable_subtype_coe.comp measurable_snd) (hf.comp measurable_fst)
  have hp : (volume : Measure I).prod volume {p : I × I | (p.2 : ℝ) = f p.1} = 0 := by
    apply Measure.measure_prod_null_of_ae_null hs
    apply Filter.Eventually.of_forall
    intro u
    exact volume_coe_eq_null (f u)
  have h := (measurePreserving_finTwoArrow (volume : Measure I)).measure_preimage hs.nullMeasurableSet
  exact h.trans hp

/-- The support of `R_b`: three line segments (graphs of `v = u`, `v = (2u + b)/4`,
`v = (2u + b)/4 + (1 - b)/2`). -/
def supportGraphs (b : ℝ) : Set (Fin 2 → I) :=
  {x | (x 1 : ℝ) = x 0} ∪ {x | (x 1 : ℝ) = (2 * (x 0 : ℝ) + b) / 4} ∪
    {x | (x 1 : ℝ) = (2 * (x 0 : ℝ) + b) / 4 + (1 - b) / 2}

theorem measurableSet_supportGraphs (b : ℝ) : MeasurableSet (supportGraphs b) := by
  have h1 : Measurable (fun x : Fin 2 → I => (x 1 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply 1)
  have h0 : Measurable (fun x : Fin 2 → I => (x 0 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply 0)
  refine ((measurableSet_eq_fun h1 h0).union (measurableSet_eq_fun h1 (by fun_prop))).union
    (measurableSet_eq_fun h1 (by fun_prop))

theorem volume_supportGraphs (b : ℝ) : (volume : Measure (Fin 2 → I)) (supportGraphs b) = 0 := by
  refine measure_union_null (measure_union_null ?_ ?_) ?_
  · exact volume_graph_null (fun u => (u : ℝ)) measurable_subtype_coe
  · exact volume_graph_null (fun u => (2 * (u : ℝ) + b) / 4) (by fun_prop)
  · exact volume_graph_null (fun u => (2 * (u : ℝ) + b) / 4 + (1 - b) / 2) (by fun_prop)

theorem Xb_mem_supportGraphs {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (p : I × Bool) :
    Xb b p ∈ supportGraphs b := by
  unfold supportGraphs Xb
  have hv := coe_Vb hb p.1 p.2
  unfold vbReal at hv
  by_cases hc : b / 2 < (p.1 : ℝ) ∧ (p.1 : ℝ) < 1 - b / 2
  · simp only [hc, and_self, ↓reduceIte] at hv
    cases hp : p.2
    · left; right
      simp [hp] at hv
      simpa using hv
    · right
      simp [hp] at hv
      simpa using hv
  · simp only [hc, ↓reduceIte] at hv
    left; left
    simpa using hv

/-- **Proposition 5.3 (i)**: `R_b` is singular: it lives on a finite union of line segments, a
Lebesgue null set. -/
theorem Rb_singular {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).toMeasure ⟂ₘ (volume : Measure (Fin 2 → I)) := by
  refine ⟨(supportGraphs b)ᶜ, (measurableSet_supportGraphs b).compl, ?_, ?_⟩
  · rw [Rb_toMeasure_eq_lawVb hb, lawVb, Measure.map_apply (measurable_Xb b)
      (measurableSet_supportGraphs b).compl]
    have : Xb b ⁻¹' (supportGraphs b)ᶜ = ∅ := by
      ext p
      simp [Xb_mem_supportGraphs hb p]
    rw [this, measure_empty]
  · rw [compl_compl]
    exact volume_supportGraphs b

/-- `R_b` has no Lebesgue density: it is not absolutely continuous. -/
theorem Rb_not_absolutelyContinuous {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    ¬ (Rb b hb).toMeasure ≪ (volume : Measure (Fin 2 → I)) := by
  intro h
  have := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h (Rb_singular hb)
  have h1 : (Rb b hb).toMeasure Set.univ = 1 := measure_univ
  rw [this] at h1
  simp at h1

end Papers.OrendayLaresRockel2026XiBeta
