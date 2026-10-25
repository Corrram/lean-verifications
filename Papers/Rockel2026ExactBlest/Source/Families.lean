import Papers.Rockel2026ExactBlest.Source.Bridge

/-! # The article's families and boundary functions are the companion's

Section 4 of the article defines the maps `T_w`, `R_b`, the copulas `A_w`, `B_b`
(copulas associated with `γ_{T_w}` and `γ^{R_b}`), the parametrization `e_b`,
the gap `Υ`, and, in Section 5, `n_b` and `Λ`. This file proves that each is the
corresponding notion of the companion development:

* `A_eq : A w = cdfOf (paperA w)`, `B_eq : B b = cdfOf (paperB b _)` for
  `b ∈ (0, 1/2)`, and `B_half : B (1/2) = A (1/2)`;
* `Upsilon_eq : Υ e = etaGap e` and `Lambda_eq : Λ n = Lambda n` on `[-1,1]`.

Each identification is proved, so the companion's results apply to the
article's statements without any choice of interpretation. -/

namespace Papers.Rockel2026ExactBlest.Source.Bridge
open Papers.Rockel2026ExactBlest.Source Proofread MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026ExactBlest (paperA paperB paperEtaB paperUpsB paperNB paperNuB etaGap graphRank
  randomRank paperR paperR_formula paperT_formula paperA_graph_law paperB_graph_law measurable_graphRank
  measurable_randomRank etaGap_paperEtaB etaGap_bottom paperEtaB_strictMonoOn paper_eta_random_extremizers
  paperNB_bijOn Lambda_paperNB)

theorem coe_projIcc_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ) = x := by
  rw [Set.coe_projIcc, min_eq_right h1, max_eq_right h0]

/-! ## Copulas associated with graph laws -/

theorem reflect_graph {f : I → I} (hf : Measurable f) (K : Copula 2)
    (hK : K.survivalCopula.toMeasure = (volume : Measure I).map (fun t => ![t, f t])) :
    K.toMeasure = (volume : Measure I).map
      (Copula.reflectPoint (Finset.univ : Finset (Fin 2)) ∘ fun t => ![t, f t]) := by
  have hg : Measurable (fun t : I => ![t, f t]) := by fun_prop
  have hr : Measurable (Copula.reflectPoint (Finset.univ : Finset (Fin 2))) := Copula.measurable_reflectPoint _
  conv_lhs => rw [← Copula.survivalCopula_survivalCopula K]
  rw [Copula.survivalCopula, Copula.toMeasure_reflect, hK, Measure.map_map hr hg]

/-- The copula associated with `γ_f` is `K` when `K`'s survival copula is the law of
`(X, f(X))`. -/
theorem assoc_gamma_eq {f : I → I} (hf : Measurable f) (K : Copula 2)
    (hK : K.survivalCopula.toMeasure = (volume : Measure I).map (fun t => ![t, f t])) :
    copulaAssociatedWith (gamma f) = cdfOf K := by
  have hg : Measurable (fun t : I => ![t, f t]) := by fun_prop
  have hr : Measurable (Copula.reflectPoint (Finset.univ : Finset (Fin 2))) := Copula.measurable_reflectPoint _
  funext u v
  simp only [copulaAssociatedWith, gamma, Prelude.leb, cdfOf, Copula.cdf]
  rw [reflect_graph hf K hK, map_measureReal_apply (hr.comp hg) measurableSet_Iic, measureReal_def]
  congr 2
  ext t
  simp [Copula.reflectPoint, Pi.le_def, Fin.forall_fin_two, ← Subtype.coe_le_coe, unitInterval.coe_symm_eq]

theorem reflect_graph_upper {f : I → I} (hf : Measurable f) (K : Copula 2)
    (hK : K.survivalCopula.toMeasure = (volume : Measure I).map (fun t => ![f t, t])) :
    K.toMeasure = (volume : Measure I).map
      (Copula.reflectPoint (Finset.univ : Finset (Fin 2)) ∘ fun t => ![f t, t]) := by
  have hg : Measurable (fun t : I => ![f t, t]) := by fun_prop
  have hr : Measurable (Copula.reflectPoint (Finset.univ : Finset (Fin 2))) := Copula.measurable_reflectPoint _
  conv_lhs => rw [← Copula.survivalCopula_survivalCopula K]
  rw [Copula.survivalCopula, Copula.toMeasure_reflect, hK, Measure.map_map hr hg]

/-- The copula associated with `γ^f` is `K` when `K`'s survival copula is the law of
`(f(Z), Z)`. -/
theorem assoc_gammaUpper_eq {f : I → I} (hf : Measurable f) (K : Copula 2)
    (hK : K.survivalCopula.toMeasure = (volume : Measure I).map (fun t => ![f t, t])) :
    copulaAssociatedWith (gammaUpper f) = cdfOf K := by
  have hg : Measurable (fun t : I => ![f t, t]) := by fun_prop
  have hr : Measurable (Copula.reflectPoint (Finset.univ : Finset (Fin 2))) := Copula.measurable_reflectPoint _
  funext u v
  simp only [copulaAssociatedWith, gammaUpper, Prelude.leb, cdfOf, Copula.cdf]
  rw [reflect_graph_upper hf K hK, map_measureReal_apply (hr.comp hg) measurableSet_Iic, measureReal_def]
  congr 2
  ext t
  simp [Copula.reflectPoint, Pi.le_def, Fin.forall_fin_two, ← Subtype.coe_le_coe, unitInterval.coe_symm_eq]

/-- A map whose graph law is a copula's survival law preserves Lebesgue measure. -/
theorem map_volume_of_graph {f : I → I} (hf : Measurable f) (K : Copula 2)
    (hK : K.survivalCopula.toMeasure = (volume : Measure I).map (fun t => ![t, f t])) :
    (volume : Measure I).map f = volume := by
  have hg : Measurable (fun t : I => ![t, f t]) := by fun_prop
  have h1 := K.survivalCopula.marginal_eq 1
  change K.survivalCopula.toMeasure.map _ = _ at h1
  rw [hK, Measure.map_map (measurable_pi_apply 1) hg] at h1
  exact h1

theorem map_volume_of_graph_upper {f : I → I} (hf : Measurable f) (K : Copula 2)
    (hK : K.survivalCopula.toMeasure = (volume : Measure I).map (fun t => ![f t, t])) :
    (volume : Measure I).map f = volume := by
  have hg : Measurable (fun t : I => ![f t, t]) := by fun_prop
  have h0 := K.survivalCopula.marginal_eq 0
  change K.survivalCopula.toMeasure.map _ = _ at h0
  rw [hK, Measure.map_map (measurable_pi_apply 0) hg] at h0
  exact h0

/-! ## `T_w` and `A_w` -/

theorem T_eq (w : I) : T w = graphRank (σ w) := by
  funext u
  apply Subtype.ext
  rw [paperT_formula]
  have hu0 := u.2.1
  have hu1 := u.2.2
  have hw0 := w.2.1
  have hw1 := w.2.2
  simp only [T]
  by_cases h : (u : ℝ) ≤ 1 - w
  · rw [ite_eq_left ⟨hu0, h⟩, ite_eq_left h, coe_projIcc_of_mem (by linarith) (by linarith)]
  · rw [ite_eq_right (fun h' => h h'.2), ite_eq_left ⟨lt_of_not_ge h, hu1⟩, ite_eq_right h,
      coe_projIcc_of_mem (by linarith) (by linarith)]

theorem measurable_T (w : I) : Measurable (T w) := by
  rw [T_eq]; exact measurable_graphRank _

theorem A_eq (w : I) : A w = cdfOf (paperA w) := by
  simp only [A, T_eq]
  exact assoc_gamma_eq (measurable_graphRank _) _ (paperA_graph_law w)

theorem copulas_A (w : I) : copulas (A w) := A_eq w ▸ copulas_cdfOf _

theorem map_volume_T (w : I) : (volume : Measure I).map (T w) = volume := by
  rw [T_eq]; exact map_volume_of_graph (measurable_graphRank _) _ (paperA_graph_law w)

/-! ## `z_b`, `R_b` and `B_b` -/

/-- The parameter `b ∈ (0, 1/2]` as a point of `[0,1]`. -/
def unitOf (b : ℝ) (h0 : 0 < b) (h1 : b ≤ 1 / 2) : I := ⟨b, h0.le, by linarith⟩

theorem symm_unitOf_gt (b : ℝ) (h0 : 0 < b) (h1 : b < 1 / 2) :
    1 / 2 < ((σ (unitOf b h0 h1.le) : I) : ℝ) := by
  rw [unitInterval.coe_symm_eq]; change 1 / 2 < 1 - b; linarith

theorem symm_unitOf_lt (b : ℝ) (h0 : 0 < b) (h1 : b < 1 / 2) :
    ((σ (unitOf b h0 h1.le) : I) : ℝ) < 1 := by
  rw [unitInterval.coe_symm_eq]; change 1 - b < 1; linarith

theorem R_eq (b : ℝ) (h0 : 0 < b) (h1 : b < 1 / 2) :
    R b = randomRank (σ (unitOf b h0 h1.le)) (symm_unitOf_gt b h0 h1) (symm_unitOf_lt b h0 h1) := by
  funext t
  apply Subtype.ext
  rw [paperR_formula (unitOf b h0 h1.le) h0 h1 t, show ((unitOf b h0 h1.le : I) : ℝ) = b from rfl]
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hz : 0 < 2 * (1 - b) := by linarith
  have hd : 0 < 1 - 2 * b := by linarith
  simp only [R, z, paperR]
  by_cases hc1 : (t : ℝ) ≤ b / (2 * (1 - b))
  · simp only [ht0, hc1, and_self, ↓reduceIte]
    have ht' := (le_div_iff₀ hz).mp hc1
    exact coe_projIcc_of_mem (by nlinarith) (by nlinarith)
  · have hc1' : b / (2 * (1 - b)) < t := lt_of_not_ge hc1
    have ht' : b < (t : ℝ) * (2 * (1 - b)) := (div_lt_iff₀ hz).mp hc1'
    by_cases hc2 : (t : ℝ) ≤ b
    · simp only [hc1, hc1', hc2, and_false, and_self, ↓reduceIte]
      apply coe_projIcc_of_mem
      · apply div_nonneg _ hd.le
        nlinarith
      · rw [div_le_iff₀ hd]; nlinarith
    · have hc2' : b < (t : ℝ) := lt_of_not_ge hc2
      simp only [hc1, hc2, hc2', ht1, and_false, and_self, ↓reduceIte]
      exact coe_projIcc_of_mem (by linarith) (by linarith)

theorem B_eq (b : ℝ) (h0 : 0 < b) (h1 : b < 1 / 2) :
    B b = cdfOf (paperB (unitOf b h0 h1.le) h1.le) := by
  simp only [B, R_eq b h0 h1]
  exact assoc_gammaUpper_eq (measurable_randomRank _ _ _) _ (paperB_graph_law (unitOf b h0 h1.le) h0 h1)

theorem measurable_R_lt (b : ℝ) (h0 : 0 < b) (h1 : b < 1 / 2) : Measurable (R b) := by
  rw [R_eq b h0 h1]; exact measurable_randomRank _ _ _

theorem map_volume_R_lt (b : ℝ) (h0 : 0 < b) (h1 : b < 1 / 2) :
    (volume : Measure I).map (R b) = volume := by
  rw [R_eq b h0 h1]
  exact map_volume_of_graph_upper (measurable_randomRank _ _ _) _ (paperB_graph_law (unitOf b h0 h1.le) h0 h1)

theorem measurable_R (b : ℝ) : Measurable (R b) := by
  unfold R
  apply continuous_projIcc.measurable.comp
  have mc : Measurable (fun t : I => (t : ℝ)) := measurable_subtype_coe
  refine Measurable.ite ?_ (by fun_prop) (Measurable.ite ?_ (by fun_prop) (Measurable.ite ?_ (by fun_prop)
    measurable_const))
  · exact (measurableSet_le measurable_const mc).inter (measurableSet_le mc measurable_const)
  · exact (measurableSet_lt measurable_const mc).inter (measurableSet_le mc measurable_const)
  · exact (measurableSet_lt measurable_const mc).inter (measurableSet_le mc measurable_const)

/-- The midpoint of `[0,1]`, as the article writes `A_{1/2}`. -/
noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

theorem z_half : z (1 / 2) = 1 / 2 := by norm_num [z]

/-- `R_{1/2}` inverts `T_{1/2}` away from the point `1/2`. -/
theorem R_T_half (x : I) (hx : x ≠ half) : R (1 / 2) (T half x) = x := by
  have hx' : (x : ℝ) ≠ 1 / 2 := fun h => hx (Subtype.ext h)
  have hx0 := x.2.1
  have hx1 := x.2.2
  apply Subtype.ext
  have hT : ((T half x : I) : ℝ) = if (x : ℝ) ≤ 1 / 2 then 1 - (x : ℝ) else (x : ℝ) - 1 / 2 := by
    rw [T_eq, paperT_formula]
    change (if (x : ℝ) ≤ 1 - 1 / 2 then 1 - (x : ℝ) else (x : ℝ) + 1 / 2 - 1) = _
    norm_num
    split_ifs <;> ring
  simp only [R, z_half]
  rw [hT]
  by_cases h : (x : ℝ) ≤ 1 / 2
  · have hlt : (x : ℝ) < 1 / 2 := lt_of_le_of_ne h hx'
    have c1 : ¬((0 : ℝ) ≤ 1 - x ∧ 1 - (x : ℝ) ≤ 1 / 2) := fun h' => by linarith [h'.2]
    have c2 : ¬((1 : ℝ) / 2 < 1 - x ∧ 1 - (x : ℝ) ≤ 1 / 2) := fun h' => by linarith [h'.2]
    have c3 : (1 : ℝ) / 2 < 1 - x ∧ 1 - (x : ℝ) ≤ 1 := ⟨by linarith, by linarith⟩
    rw [ite_eq_left h, ite_eq_right c1, ite_eq_right c2, ite_eq_left c3,
      coe_projIcc_of_mem (by linarith) (by linarith)]
    ring
  · have hgt : 1 / 2 < (x : ℝ) := lt_of_not_ge h
    have c1 : (0 : ℝ) ≤ x - 1 / 2 ∧ (x : ℝ) - 1 / 2 ≤ 1 / 2 := ⟨by linarith, by linarith⟩
    rw [ite_eq_right h, ite_eq_left c1, coe_projIcc_of_mem (by linarith) (by linarith)]
    ring

theorem volume_singleton_I (p : I) : (volume : Measure I) {p} = 0 := by
  rw [← Set.Icc_self, unitInterval.volume_Icc, sub_self, ENNReal.ofReal_zero]

/-- `B_{1/2} = A_{1/2}`: `γ^{R_{1/2}}` and `γ_{T_{1/2}}` agree on rectangles. -/
theorem B_half : B (1 / 2) = A half := by
  funext u v
  simp only [B, A, copulaAssociatedWith, gamma, gammaUpper, Prelude.leb]
  congr 1
  have hT := map_volume_T half
  have hmT := measurable_T half
  have hmR := measurable_R (1 / 2)
  have mc : Measurable (fun t : I => (t : ℝ)) := measurable_subtype_coe
  have hS : MeasurableSet {t : I | 1 - (R (1 / 2) t : ℝ) ≤ u ∧ 1 - (t : ℝ) ≤ v} :=
    (measurableSet_le (measurable_const.sub (mc.comp hmR)) measurable_const).inter
      (measurableSet_le (measurable_const.sub mc) measurable_const)
  conv_lhs => rw [← hT, Measure.map_apply hmT hS]
  refine measure_congr ?_
  have hae : ∀ᵐ x ∂(volume : Measure I), x ≠ half := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using volume_singleton_I half
  filter_upwards [hae] with x hx
  change (1 - (R (1 / 2) (T half x) : ℝ) ≤ u ∧ 1 - (T half x : ℝ) ≤ v) =
    (1 - (x : ℝ) ≤ u ∧ 1 - (T half x : ℝ) ≤ v)
  rw [R_T_half x hx]

theorem B_half_eq : B (1 / 2) = cdfOf (paperA half) := B_half.trans (A_eq half)

theorem map_volume_R_half : (volume : Measure I).map (R (1 / 2)) = volume := by
  have hT := map_volume_T half
  have hmT := measurable_T half
  have hae : (R (1 / 2)) ∘ (T half) =ᵐ[volume] id := by
    have hne : ∀ᵐ x ∂(volume : Measure I), x ≠ half := by
      rw [ae_iff]
      simpa only [not_not, Set.ofPred_eq_eq_singleton] using volume_singleton_I half
    filter_upwards [hne] with x hx
    exact R_T_half x hx
  conv_lhs => rw [← hT]
  rw [Measure.map_map (measurable_R _) hmT, Measure.map_congr hae, Measure.map_id]

/-! ## The parametrization `e_b` and the gap `Υ` -/

theorem e_eq (b : ℝ) : e b = paperEtaB b := rfl

theorem paperEtaB_injOn : InjOn paperEtaB (Ioo 0 (1 / 2)) :=
  paperEtaB_strictMonoOn.injOn.mono Ioo_subset_Icc_self

/-- A definite description with exactly one solution denotes it. -/
theorem epsilon_eq_of_unique {α : Type} [Nonempty α] {P : α → Prop} {a : α} (ha : P a)
    (hu : ∀ b, P b → b = a) : Classical.epsilon P = a :=
  hu _ (Classical.epsilon_spec ⟨a, ha⟩)

theorem Upsilon_param (x : ℝ) (hx : -1 < x ∧ x < -(3 / 4)) :
    (Classical.epsilon fun y : ℝ => ∃ b, (0 < b ∧ b < 1 / 2) ∧ e b = x ∧
      y = b ^ 3 * (6 * b ^ 2 - 15 * b + 8) / (8 * (1 - b) ^ 2)) = etaGap x := by
  obtain ⟨b, hb, hb0, hpe, -⟩ := paper_eta_random_extremizers x ⟨hx.1, by linarith [hx.2]⟩
  have hgap : etaGap x = paperUpsB b := by rw [← hpe]; exact etaGap_paperEtaB b hb0 hb
  rw [hgap]
  apply epsilon_eq_of_unique ⟨b, ⟨hb0, hb⟩, hpe, rfl⟩
  rintro y ⟨c, hc, hce, rfl⟩
  have : c = b := paperEtaB_injOn hc ⟨hb0, hb⟩ (hce.trans hpe.symm)
  subst this
  rfl

theorem Upsilon_eq (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : Upsilon x = etaGap x := by
  unfold Upsilon
  by_cases h1 : x = -1
  · subst h1; rw [ite_eq_left rfl, etaGap_bottom]
  · rw [ite_eq_right h1]
    by_cases h2 : -(3 / 4) ≤ x ∧ x ≤ 1
    · rw [ite_eq_left h2]
      unfold etaGap Papers.Rockel2026ExactBlest.graphGap
      rw [ite_eq_right (by linarith [h2.1])]
      norm_num
    · have h3 : -1 < x ∧ x < -(3 / 4) :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm h1), by
          by_contra hc; exact h2 ⟨le_of_not_gt hc, hx.2⟩⟩
      rw [ite_eq_right h2, ite_eq_left h3]
      exact Upsilon_param x h3

/-! ## `n_b` and `Λ` -/

theorem n_eq (b : ℝ) : n b = paperNB b := rfl

theorem Lambda_param (x : ℝ) (hx : -1 < x ∧ x < -(7 / 8)) :
    (Classical.epsilon fun y : ℝ => ∃ b, (0 < b ∧ b < 1 / 2) ∧ n b = x ∧
      y = -1 + (2 - b) * b ^ 3 / (1 - b)) = Papers.Rockel2026ExactBlest.Lambda x := by
  obtain ⟨hmono, hbij⟩ := paperNB_bijOn
  obtain ⟨b, hb, hbx⟩ := hbij.surjOn ⟨hx.1, by linarith [hx.2]⟩
  have hL : Papers.Rockel2026ExactBlest.Lambda x = paperNuB b := by
    rw [← hbx]; exact Lambda_paperNB b hb.1 hb.2
  rw [hL]
  apply epsilon_eq_of_unique ⟨b, hb, hbx, rfl⟩
  rintro y ⟨c, hc, hcx, rfl⟩
  have : c = b := hmono.injOn hc hb (hcx.trans hbx.symm)
  subst this
  rfl

theorem Lambda_eq (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) : Lambda x = Papers.Rockel2026ExactBlest.Lambda x := by
  unfold Lambda
  by_cases h1 : x = -1
  · subst h1; rw [ite_eq_left rfl, Papers.Rockel2026ExactBlest.Lambda_neg_one]
  · rw [ite_eq_right h1]
    by_cases h2 : -(7 / 8) ≤ x ∧ x ≤ 1
    · rw [ite_eq_left h2, Papers.Rockel2026ExactBlest.Lambda_closed_branch x (by linarith [h2.1])]
      unfold Papers.Rockel2026ExactBlest.lambdaClosed
      norm_num
    · have h3 : -1 < x ∧ x < -(7 / 8) :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm h1), by
          by_contra hc; exact h2 ⟨le_of_not_gt hc, hx.2⟩⟩
      rw [ite_eq_right h2, ite_eq_left h3]
      exact Lambda_param x h3

end Papers.Rockel2026ExactBlest.Source.Bridge
