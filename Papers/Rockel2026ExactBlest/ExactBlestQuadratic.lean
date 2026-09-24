import Papers.Rockel2026ExactBlest.ExactBlestRearrangement

/-! The distribution-function rank map used in the rho/Blest rearrangement proof. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology
namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

def quadraticScore (c : ℝ) (x : I) : ℝ := ((x : ℝ) - c) ^ 2
def quadraticLaw (c : ℝ) : Measure ℝ := (volume : Measure I).map (quadraticScore c)

theorem uniform_real_level_null (r : ℝ) : (volume : Measure I) {x | (x : ℝ) = r} = 0 := by
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  exact Subtype.ext (hx.trans hy.symm)

instance quadraticLaw_probability (c : ℝ) : IsProbabilityMeasure (quadraticLaw c) := by
  unfold quadraticLaw
  infer_instance

instance quadraticLaw_atomless (c : ℝ) : NullSingletonClass (quadraticLaw c) := by
  constructor
  intro r
  rw [quadraticLaw, Measure.map_apply (by unfold quadraticScore; fun_prop) (measurableSet_singleton r)]
  change (volume : Measure I) {x | quadraticScore c x = r} = 0
  by_cases he : ({x : I | quadraticScore c x = r}).Nonempty
  · obtain ⟨y, hy⟩ := he
    have hs : {x : I | quadraticScore c x = r} ⊆
        {x | (x : ℝ) = y} ∪ {x | (x : ℝ) = 2 * c - y} := by
      intro x hx
      change quadraticScore c x = r at hx
      change quadraticScore c y = r at hy
      have hp : ((x : ℝ) - y) * ((x : ℝ) + y - 2 * c) = 0 := by
        unfold quadraticScore at hx hy
        nlinarith
      rcases mul_eq_zero.mp hp with h | h
      · left; change (x : ℝ) = y; linarith
      · right; change (x : ℝ) = 2 * c - y; linarith
    exact measure_mono_null hs (measure_union_null (uniform_real_level_null y) (uniform_real_level_null (2 * c - y)))
  · rw [Set.not_nonempty_iff_eq_empty.mp he, measure_empty]

theorem continuous_quadratic_cdf (c : ℝ) : Continuous (ProbabilityTheory.cdf (quadraticLaw c)) :=
  continuous_cdf_of_atomless _

def quadraticRank (c : ℝ) (x : I) : I := cdfUnit (quadraticLaw c) (quadraticScore c x)

theorem quadraticRank_uniform (c : ℝ) : MeasurePreserving (quadraticRank c) volume volume := by
  exact cdfRank_uniform (quadraticScore c) (by unfold quadraticScore; fun_prop) (continuous_quadratic_cdf c)

theorem quadratic_cdf_at_score (c x : I) :
    ProbabilityTheory.cdf (quadraticLaw c) (quadraticScore c x) =
      min 1 ((c : ℝ) + |(x : ℝ) - c|) - max 0 ((c : ℝ) - |(x : ℝ) - c|) := by
  let r := |(x : ℝ) - c|
  have hr : 0 ≤ r := abs_nonneg _
  let l : I := ⟨max 0 ((c : ℝ) - r), le_max_left _ _, max_le (by norm_num) (by linarith [c.property.2])⟩
  let u : I := ⟨min 1 ((c : ℝ) + r), le_min (by norm_num) (by linarith [c.property.1]), min_le_left _ _⟩
  have hpre : quadraticScore c ⁻¹' Iic (quadraticScore c x) = Icc l u := by
    ext y
    change ((y : ℝ) - c) ^ 2 ≤ ((x : ℝ) - c) ^ 2 ↔
      max 0 ((c : ℝ) - r) ≤ (y : ℝ) ∧ (y : ℝ) ≤ min 1 ((c : ℝ) + r)
    rw [sq_le_sq, abs_le, max_le_iff, le_min_iff]
    dsimp [r]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨y.property.1, by linarith⟩, ⟨y.property.2, by linarith⟩⟩
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact ⟨by linarith, by linarith⟩
  have hlu : (l : ℝ) ≤ u := by
    dsimp [l, u]
    exact (max_le c.property.1 (by linarith)).trans (le_min c.property.2 (by linarith))
  rw [ProbabilityTheory.cdf_eq_real, quadraticLaw,
    map_measureReal_apply (by unfold quadraticScore; fun_prop) measurableSet_Iic, hpre]
  simp only [Measure.real, unitInterval.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hlu)]
  rfl

theorem quadraticRank_paper (c x : I) :
    (quadraticRank c x : ℝ) =
      if |(x : ℝ) - c| ≤ min (c : ℝ) (1 - (c : ℝ)) then 2 * |(x : ℝ) - c|
      else if 2 * (c : ℝ) ≤ x then (x : ℝ) else 1 - (x : ℝ) := by
  change ProbabilityTheory.cdf (quadraticLaw c) (quadraticScore c x) = _
  rw [quadratic_cdf_at_score]
  have hc0 := c.property.1
  have hc1 := c.property.2
  have hx0 := x.property.1
  have hx1 := x.property.2
  by_cases h : |(x : ℝ) - c| ≤ min (c : ℝ) (1 - (c : ℝ))
  · rw [ite_eq_left h]
    have h1 := h.trans (min_le_left _ _)
    have h2 := h.trans (min_le_right _ _)
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    ring
  · rw [ite_eq_right h]
    by_cases hx : (c : ℝ) ≤ x
    · rw [abs_of_nonneg (sub_nonneg.mpr hx)] at h ⊢
      have hc : 2 * (c : ℝ) ≤ x := by
        by_contra hn
        apply h
        exact le_min (by linarith) (by linarith)
      rw [ite_eq_left hc, min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
    · rw [abs_of_nonpos (by linarith)] at h ⊢
      have hc : (x : ℝ) ≤ 2 * c - 1 := by
        by_contra hn
        apply h
        exact le_min (by linarith) (by linarith)
      rw [ite_eq_right (by linarith), min_eq_left (by linarith), max_eq_right (by linarith)]
      ring

theorem quadraticRank_positive (c : I) (hc : (c : ℝ) ≤ 1 / 2) (x : I) :
    quadraticRank c x = rhoRank ⟨2 * c, by constructor <;> linarith [c.property.1]⟩ x := by
  apply Subtype.ext
  change ProbabilityTheory.cdf (quadraticLaw c) (quadraticScore c x) = _
  rw [quadratic_cdf_at_score]
  dsimp only [rhoRank]
  have hc0 := c.property.1
  have hx0 := x.property.1
  have hx1 := x.property.2
  have he : (2 * (c : ℝ)) / 2 = c := by ring
  rw [he]
  by_cases hx : (c : ℝ) ≤ x
  · rw [abs_of_nonneg (sub_nonneg.mpr hx)]
    grind
  · rw [abs_of_nonpos (by linarith)]
    grind

theorem quadraticRank_symm (c x : I) :
    quadraticRank c (unitInterval.symm x) = quadraticRank (unitInterval.symm c) x := by
  apply Subtype.ext
  change ProbabilityTheory.cdf (quadraticLaw c) (quadraticScore c (unitInterval.symm x)) =
    ProbabilityTheory.cdf (quadraticLaw (unitInterval.symm c)) (quadraticScore (unitInterval.symm c) x)
  rw [quadratic_cdf_at_score, quadratic_cdf_at_score]
  simp only [unitInterval.coe_symm_eq]
  have he : 1 - (x : ℝ) - c = -((x : ℝ) - (1 - (c : ℝ))) := by ring
  rw [he, abs_neg]
  grind

theorem survival_reflect_first (C : Copula 2) :
    (C.reflect {0}).survivalCopula = C.survivalCopula.reflect {0} := by
  apply Copula.ext
  simp only [Copula.survivalCopula, Copula.toMeasure_reflect]
  rw [Measure.map_map (Copula.measurable_reflectPoint _) (Copula.measurable_reflectPoint _),
    Measure.map_map (Copula.measurable_reflectPoint _) (Copula.measurable_reflectPoint _)]
  congr 1
  ext x i
  fin_cases i <;> simp [Copula.reflectPoint]

def rhoFullFamily (c : I) : Copula 2 :=
  if hc : (c : ℝ) ≤ 1 / 2 then
    rhoFamily ⟨2 * c, by constructor <;> linarith [c.property.1]⟩
  else (rhoFamily ⟨2 * (1 - (c : ℝ)), by constructor <;> linarith [c.property.2]⟩).reflect {0}

theorem rhoFullFamily_values (c : I) :
    (rhoFullFamily c).spearmanRho =
      (if (c : ℝ) ≤ 1 / 2 then 1 - 8 * (c : ℝ) ^ 3 else 8 * (1 - (c : ℝ)) ^ 3 - 1) ∧
    Papers.Rockel2026XiBlest.blestNu (rhoFullFamily c) =
      (if (c : ℝ) ≤ 1 / 2 then 1 - 12 * (c : ℝ) ^ 4
       else 16 * (1 - (c : ℝ)) ^ 3 - 12 * (1 - (c : ℝ)) ^ 4 - 1) := by
  unfold rhoFullFamily
  split_ifs with hc
  · rw [(rho_family_values _).1, (rho_family_values _).2]
    unfold rhoPosR rhoPosN
    constructor <;> ring
  · rw [Copula.spearmanRho_reflect_first, nu_reflect_first,
      (rho_family_values _).1, (rho_family_values _).2]
    unfold rhoPosR rhoPosN
    constructor <;> ring

theorem rhoFullFamily_graph (c : I) :
    ∀ᵐ x ∂(rhoFullFamily c).survivalCopula.toMeasure, x 1 = quadraticRank c (x 0) := by
  by_cases hc : (c : ℝ) ≤ 1 / 2
  · simp only [rhoFullFamily, dite_eq_left hc]
    have h := rho_upper_graph (rhoFamily ⟨2 * c, by constructor <;> linarith [c.property.1]⟩)
      _ (rho_family_values _).1 (rho_family_values _).2
    filter_upwards [h] with x hx
    rw [quadraticRank_positive c hc]
    exact hx
  · simp only [rhoFullFamily, dite_eq_right hc]
    rw [survival_reflect_first, Copula.toMeasure_reflect]
    have hm := (quadraticRank_uniform (c : ℝ)).measurable
    apply (ae_map_iff (Copula.measurable_reflectPoint _).aemeasurable
      (measurableSet_eq_fun (measurable_pi_apply 1) (hm.comp (measurable_pi_apply 0)))).mpr
    have h := rho_upper_graph (rhoFamily ⟨2 * (1 - (c : ℝ)), by constructor <;> linarith [c.property.2]⟩)
      _ (rho_family_values _).1 (rho_family_values _).2
    filter_upwards [h] with x hx
    change x 1 = quadraticRank c (unitInterval.symm (x 0))
    rw [quadraticRank_symm]
    rw [quadraticRank_positive (unitInterval.symm c) (by change 1 - (c : ℝ) ≤ 1 / 2; linarith)]
    exact hx

theorem rhoFullFamily_graph_law (c : I) :
    (rhoFullFamily c).survivalCopula.toMeasure =
      (volume : Measure I).map (fun x => ![x, quadraticRank c x]) := by
  let E := (rhoFullFamily c).survivalCopula
  have hm : Measurable (fun x : I => ![x, quadraticRank c x]) := by
    have := (quadraticRank_uniform (c : ℝ)).measurable
    fun_prop
  rw [← E.map_eval 0, Measure.map_map hm (measurable_pi_apply 0)]
  have he : (fun x : Fin 2 → I => ![x 0, quadraticRank c (x 0)]) =ᵐ[E.toMeasure] id := by
    filter_upwards [rhoFullFamily_graph c] with x hx
    funext i
    fin_cases i
    · rfl
    · exact hx.symm
  change E.toMeasure = E.toMeasure.map (fun x => ![x 0, quadraticRank c (x 0)])
  rw [Measure.map_congr he, Measure.map_id]

theorem quadraticRank_endpoints (x : I) :
    quadraticRank 0 x = x ∧ quadraticRank 1 x = unitInterval.symm x := by
  constructor
  · apply Subtype.ext
    change ProbabilityTheory.cdf (quadraticLaw (0 : I)) (quadraticScore (0 : I) x) = (x : ℝ)
    rw [quadratic_cdf_at_score]
    simp [abs_of_nonneg x.property.1, min_eq_right x.property.2, x.property.1]
  · apply Subtype.ext
    change ProbabilityTheory.cdf (quadraticLaw (1 : I)) (quadraticScore (1 : I) x) = 1 - (x : ℝ)
    rw [quadratic_cdf_at_score]
    change min 1 (1 + |(x : ℝ) - 1|) - max 0 (1 - |(x : ℝ) - 1|) = 1 - (x : ℝ)
    rw [abs_of_nonpos (by linarith [x.property.2])]
    have hx0 := x.property.1
    have hx1 := x.property.2
    grind

theorem quadraticRank_half (x : I) :
    (quadraticRank (Copula.unitHalf : ℝ) x : ℝ) = |2 * (x : ℝ) - 1| := by
  rw [quadraticRank_positive Copula.unitHalf (by norm_num [Copula.unitHalf])]
  change (if (x : ℝ) ≤ 2 * (1 / 2 : ℝ) then 2 * |(x : ℝ) - (2 * (1 / 2 : ℝ)) / 2| else (x : ℝ)) = _
  norm_num
  rw [ite_eq_left x.property.2]
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring
  · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    ring

theorem rho_midpoint_reflected_graph :
    ∀ᵐ x ∂(rhoFullFamily Copula.unitHalf).survivalCopula.toMeasure,
      (x 1 : ℝ) = |2 * (x 0 : ℝ) - 1| := by
  filter_upwards [rhoFullFamily_graph Copula.unitHalf] with x hx
  rw [hx]
  exact quadraticRank_half (x 0)

theorem rho_midpoint_original_graph :
    ∀ᵐ x ∂(rhoFullFamily Copula.unitHalf).toMeasure,
      (x 1 : ℝ) = min (2 * (x 0 : ℝ)) (2 - 2 * (x 0 : ℝ)) := by
  let C := rhoFullFamily Copula.unitHalf
  let p := fun x : Fin 2 → I => (x 1 : ℝ) = min (2 * (x 0 : ℝ)) (2 - 2 * (x 0 : ℝ))
  have hp : MeasurableSet {x | p x} := measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have h : ∀ᵐ x ∂C.survivalCopula.toMeasure.map (Copula.reflectPoint Finset.univ), p x := by
    apply (ae_map_iff (Copula.measurable_reflectPoint _).aemeasurable hp).mpr
    filter_upwards [rho_midpoint_reflected_graph] with x hx
    change 1 - (x 1 : ℝ) = min (2 * (1 - (x 0 : ℝ))) (2 - 2 * (1 - (x 0 : ℝ)))
    rw [hx]
    by_cases hx0 : 0 ≤ 2 * (x 0 : ℝ) - 1
    · rw [abs_of_nonneg hx0]; grind
    · rw [abs_of_nonpos (le_of_not_ge hx0)]; grind
  change ∀ᵐ x ∂C.survivalCopula.survivalCopula.toMeasure, p x at h
  simpa only [Copula.survivalCopula_survivalCopula] using h

#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticRank_endpoints
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticRank_half
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_midpoint_reflected_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_midpoint_original_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticRank_positive
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticRank_symm
#assert_standard_axioms Papers.Rockel2026ExactBlest.survival_reflect_first
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_values
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.rhoFullFamily_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.uniform_real_level_null
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticLaw_probability
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticLaw_atomless
#assert_standard_axioms Papers.Rockel2026ExactBlest.continuous_quadratic_cdf
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticRank_uniform
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadratic_cdf_at_score
#assert_standard_axioms Papers.Rockel2026ExactBlest.quadraticRank_paper
end
end Papers.Rockel2026ExactBlest
