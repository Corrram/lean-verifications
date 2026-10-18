import Papers.Rockel2026ExactBlest.Source.Article
import Mathlib

/-! # The proof of Corollary 3.2, sentence by sentence

Each theorem `claimK : obligationK` proves one compiled sentence of the proof of
Corollary 3.2 (claims 14–25) or a part of its statement (claims 11–13) from
exactly the premises the text makes available: the results it cites and the
earlier sentences of the same proof. `obligationK` is generated from the
article; this file only supplies the reasoning between sentences.

This module imports nothing but the compiled article (and through it Mathlib),
so it cannot use the paper's companion Lean results; `#mirror_certify` audits
this as well. -/

namespace Papers.Rockel2026ExactBlest.Source.Proofs
open Papers.Rockel2026ExactBlest.Source LeanMirror.Tex MeasureTheory
open scoped unitInterval

/-- The point `1/2` of `[0,1]`, as the article's `D_{1/2}` writes it. -/
local notation "half" => Set.projIcc (0 : ℝ) 1 zero_le_one (1 / 2)

theorem coe_half : ((half : I) : ℝ) = 1 / 2 := by
  rw [Set.coe_projIcc]; norm_num

theorem coe_projIcc_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ) = x := by
  rw [Set.coe_projIcc, min_eq_right h1, max_eq_right h0]

theorem coe_reflect (w : I) : ((Set.projIcc (0 : ℝ) 1 zero_le_one (1 - (w : ℝ)) : I) : ℝ) = 1 - w :=
  coe_projIcc_of_mem (by linarith [w.2.2]) (by linarith [w.2.1])

/-- The survival transform defined in the article is an involution. -/
theorem survival_survival (C : I → I → ℝ) : survival (survival C) = C := by
  funext u v
  simp only [survival, coe_reflect, sub_sub_cancel, Set.projIcc_val]
  ring

theorem measurable_tentMap : Measurable tentMap := by
  unfold tentMap
  exact (continuous_projIcc.comp (by fun_prop)).measurable

theorem measurable_absMap :
    Measurable (fun x : I => Set.projIcc (0 : ℝ) 1 zero_le_one |2 * (x : ℝ) - 1|) :=
  (continuous_projIcc.comp (by fun_prop)).measurable

theorem abs_bounds (x : I) : 0 ≤ |2 * (x : ℝ) - 1| ∧ |2 * (x : ℝ) - 1| ≤ 1 :=
  ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [x.2.1], by linarith [x.2.2]⟩⟩

/-! ## Measure facts on `[0,1]` -/

theorem volume_level (r : ℝ) : (volume : Measure I) {t | (t : ℝ) = r} = 0 := by
  by_cases hr : r ∈ Set.Icc (0 : ℝ) 1
  · have : {t : I | (t : ℝ) = r} = Set.Icc ⟨r, hr⟩ ⟨r, hr⟩ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_Icc]
      constructor
      · intro h; exact ⟨le_of_eq (Subtype.ext h).symm, le_of_eq (Subtype.ext h)⟩
      · intro h; exact congrArg Subtype.val (le_antisymm h.2 h.1)
    rw [this, unitInterval.volume_Icc, sub_self, ENNReal.ofReal_zero]
  · have : {t : I | (t : ℝ) = r} = ∅ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h; exact hr (h ▸ t.2)
    rw [this, measure_empty]

theorem measure_eq_of_squeeze {s t n : Set I} (h1 : s ⊆ t) (h2 : t ⊆ s ∪ n)
    (hn : (volume : Measure I) n = 0) : (volume : Measure I) s = volume t :=
  le_antisymm (measure_mono h1)
    ((measure_mono h2).trans ((measure_union_le _ _).trans (by rw [hn, add_zero])))

/-- Inclusion–exclusion for the survival transform of a graph law. -/
theorem survival_graph (f : I → I) (hf : Measurable f)
    (hlaw : ∀ v : I, (volume : Measure I) {t | (f t : ℝ) ≤ v} = ENNReal.ofReal v)
    (hnull : ∀ v : ℝ, (volume : Measure I) {t | (f t : ℝ) = v} = 0) (u v : I) :
    (u : ℝ) + v - 1 + ((volume : Measure I) {t | (u : ℝ) ≤ t ∧ (v : ℝ) ≤ f t}).toReal =
      ((volume : Measure I) {t | (t : ℝ) ≤ u ∧ (f t : ℝ) ≤ v}).toReal := by
  have mf : Measurable (fun t : I => (f t : ℝ)) := measurable_subtype_coe.comp hf
  have mc : Measurable (fun t : I => (t : ℝ)) := measurable_subtype_coe
  set A : Set I := {t | (t : ℝ) < u}
  set B : Set I := {t | (f t : ℝ) < v}
  have hA : MeasurableSet A := measurableSet_lt mc measurable_const
  have hB : MeasurableSet B := measurableSet_lt mf measurable_const
  have hT : {t : I | (u : ℝ) ≤ t ∧ (v : ℝ) ≤ f t} = (A ∪ B)ᶜ := by
    ext t; simp [A, B, not_lt]
  have hAu : (volume : Measure I).real A = u := by
    have : A = Set.Iio u := by ext t; simp [A, Subtype.coe_lt_coe]
    rw [this, measureReal_def, unitInterval.volume_Iio, ENNReal.toReal_ofReal u.2.1]
  have hBv : (volume : Measure I).real B = v := by
    rw [measureReal_def, measure_eq_of_squeeze (s := B) (t := {t | (f t : ℝ) ≤ v}) (n := {t | (f t : ℝ) = v})
      (fun t (ht : (f t : ℝ) < v) => show (f t : ℝ) ≤ v from le_of_lt ht) (fun t ht => ?_) (hnull v),
      hlaw v, ENNReal.toReal_ofReal v.2.1]
    rcases lt_or_eq_of_le (show (f t : ℝ) ≤ v from ht) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hAB : (volume : Measure I).real (A ∩ B) =
      ((volume : Measure I) {t | (t : ℝ) ≤ u ∧ (f t : ℝ) ≤ v}).toReal := by
    rw [measureReal_def, measure_eq_of_squeeze (s := A ∩ B) (t := {t | (t : ℝ) ≤ u ∧ (f t : ℝ) ≤ v})
      (n := {t | (t : ℝ) = u} ∪ {t | (f t : ℝ) = v})
      (fun t (ht : (t : ℝ) < u ∧ (f t : ℝ) < v) =>
        show (t : ℝ) ≤ u ∧ (f t : ℝ) ≤ v from ⟨le_of_lt ht.1, le_of_lt ht.2⟩) (fun t ht => ?_)
      (measure_union_null (volume_level _) (hnull _))]
    rcases lt_or_eq_of_le ht.1 with h1 | h1
    · rcases lt_or_eq_of_le ht.2 with h2 | h2
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr h2)
    · exact Or.inr (Or.inl h1)
  have hU := measureReal_union_add_inter (μ := (volume : Measure I)) (s := A) hB
  have hC := measureReal_compl (μ := (volume : Measure I)) (hA.union hB)
  rw [hT, ← measureReal_def, hC, probReal_univ, ← hAB]
  linarith

/-! ## The sentences of the proof -/

theorem proof14 : obligation14 := by
  intro _ _
  refine ⟨fun x hx => ⟨⟨hx.1, by linarith [hx.2]⟩, by norm_num, by linarith [hx.1], by norm_num⟩,
    fun x hx => ?_⟩
  simp only [Phi, ite_eq_left hx]
  ring

theorem hasDerivAt_left (x : ℝ) :
    HasDerivAt (fun y : ℝ => y + 1 - 3 / 4 * (1 + y) ^ (4 / 3 : ℝ)) (1 - (1 + x) ^ (1 / 3 : ℝ)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := HasDerivAt.const_add 1 (hasDerivAt_id' x)
  have h2 := HasDerivAt.const_mul (3 / 4 : ℝ)
    (HasDerivAt.rpow_const (p := 4 / 3) h1 (Or.inr (by norm_num)))
  have h3 := HasDerivAt.sub (HasDerivAt.add_const 1 (hasDerivAt_id' x)) h2
  convert h3 using 1
  norm_num
  ring

theorem hasDerivAt_right (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - y - 3 / 4 * (1 - y) ^ (4 / 3 : ℝ)) ((1 - x) ^ (1 / 3 : ℝ) - 1) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := HasDerivAt.const_sub 1 (hasDerivAt_id' x)
  have h2 := HasDerivAt.const_mul (3 / 4 : ℝ)
    (HasDerivAt.rpow_const (p := 4 / 3) h1 (Or.inr (by norm_num)))
  have h3 := HasDerivAt.sub (HasDerivAt.const_sub 1 (hasDerivAt_id' x)) h2
  convert h3 using 1
  norm_num
  ring

theorem proof15 : obligation15 := by
  intro _ _ _
  refine ⟨fun x hx => ⟨⟨fun y hy => ⟨by norm_num, by linarith [hy.1], by norm_num⟩,
      by linarith [hx.1], by norm_num⟩, fun _ _ => ⟨by linarith [hx.1], by norm_num⟩⟩,
    fun x hx => ⟨(hasDerivAt_left x).hasDerivWithinAt, fun hneg => ?_⟩⟩
  have : (1 + x) ^ (1 / 3 : ℝ) < 1 :=
    Real.rpow_lt_one (by linarith [hx.1]) (by linarith) (by norm_num)
  linarith

theorem proof16 : obligation16 := by
  intro _ _ _ _
  refine ⟨fun x hx => ⟨⟨by linarith [hx.1], hx.2⟩, by norm_num, by linarith [hx.2], by norm_num⟩,
    fun x hx => ?_⟩
  unfold Phi
  by_cases h : -1 ≤ x ∧ x ≤ 0
  · have hx0 : x = 0 := le_antisymm h.2 hx.1
    subst hx0
    rw [ite_eq_left h]
    norm_num
  · rw [ite_eq_right h, ite_eq_left hx]
    ring

theorem proof17 : obligation17 := by
  intro _ _ _ _ _
  refine ⟨fun x hx => ⟨⟨fun y hy => ⟨by norm_num, by linarith [hy.2], by norm_num⟩,
      by linarith [hx.2], by norm_num⟩, fun _ _ => ⟨by linarith [hx.2], by norm_num⟩⟩,
    fun x hx => ⟨(hasDerivAt_right x).hasDerivWithinAt, fun hpos => ?_⟩⟩
  have : (1 - x) ^ (1 / 3 : ℝ) < 1 :=
    Real.rpow_lt_one (by linarith [hx.2]) (by linarith) (by norm_num)
  linarith

theorem proof18 : obligation18 := by
  intro_premises
  unfold claim14 at c14
  unfold claim15 at c15
  unfold claim16 at c16
  unfold claim17 at c17
  set g : ℝ → ℝ := fun y => y + 1 - 3 / 4 * (1 + y) ^ (4 / 3 : ℝ) with hg
  set h : ℝ → ℝ := fun y => 1 - y - 3 / 4 * (1 - y) ^ (4 / 3 : ℝ) with hh
  have gmono : StrictMonoOn g (Set.Icc (-1) 0) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) (f' := fun y => 1 - (1 + y) ^ (1 / 3 : ℝ))
    · intro y hy
      exact (c15 y hy).1.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy ⊢
      exact (c15 y (Set.Ioo_subset_Icc_self hy)).1.mono Set.Ioo_subset_Icc_self
    · intro y hy
      rw [interior_Icc] at hy
      exact (c15 y (Set.Ioo_subset_Icc_self hy)).2 hy.2
  have hanti : StrictAntiOn h (Set.Icc 0 1) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _) (f' := fun y => (1 - y) ^ (1 / 3 : ℝ) - 1)
    · intro y hy
      exact (c17 y hy).1.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy ⊢
      exact (c17 y (Set.Ioo_subset_Icc_self hy)).1.mono Set.Ioo_subset_Icc_self
    · intro y hy
      rw [interior_Icc] at hy
      exact (c17 y (Set.Ioo_subset_Icc_self hy)).2 hy.1
  have hPhi0 : Phi 0 = 1 / 4 := by
    have := c14 0 ⟨by norm_num, le_refl 0⟩
    norm_num at this
    linarith
  have g0 : g 0 = 1 / 4 := by simp [hg]; norm_num
  have h0 : h 0 = 1 / 4 := by simp [hh]; norm_num
  have m0 : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 0 := ⟨by norm_num, le_refl 0⟩
  have m0' : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, by norm_num⟩
  refine ⟨fun x hx => ⟨⟨⟨hx, by norm_num, by norm_num⟩, fun _ => ⟨⟨by norm_num, by norm_num⟩, by norm_num⟩⟩,
    fun _ => ⟨hx, by norm_num, by norm_num⟩⟩, fun x hx => ?_⟩
  rcases le_total x 0 with hx0 | hx0
  · have mx : x ∈ Set.Icc (-1 : ℝ) 0 := ⟨hx.1, hx0⟩
    have e : Phi x - x = g x := c14 x mx
    refine ⟨⟨?_, hPhi0⟩, fun heq => ?_⟩
    · rw [e, hPhi0, ← g0]
      exact gmono.monotoneOn mx m0 hx0
    · rw [e, hPhi0, ← g0] at heq
      exact gmono.injOn mx m0 heq
  · have mx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx.2⟩
    have e : Phi x - x = h x := c16 x mx
    refine ⟨⟨?_, hPhi0⟩, fun heq => ?_⟩
    · rw [e, hPhi0, ← h0]
      exact hanti.antitoneOn m0' mx hx0
    · rw [e, hPhi0, ← h0] at heq
      exact hanti.injOn mx m0' heq

theorem proof19 : obligation19 := by
  intro_premises
  refine ⟨⟨⟨by norm_num, by norm_num, by norm_num⟩, (m10 _).1, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  unfold claim19
  unfold claim8 at c8
  rw [(c8 _).1, coe_half]
  norm_num

theorem proof20 : obligation20 := by
  intro_premises
  unfold claim3 at c3
  unfold claim4 at c4
  unfold claim10 at c10
  unfold claim18 at c18
  unfold claim19 at c19
  have hD := m19.2.1
  refine ⟨fun C hC => ⟨⟨⟨hC, hC⟩, by norm_num⟩, fun _ => ⟨by norm_num, by norm_num, by norm_num⟩⟩, ?_⟩
  intro C hC hgap
  obtain ⟨⟨hr, -⟩, -, hup⟩ := (c3 (rho C) (nu C)).1 ⟨C, hC, rfl, rfl⟩
  have h18 := c18 (rho C) hr
  have hPhi0 : Phi 0 = 1 / 4 := h18.1.2
  have hr0 : rho C = 0 := h18.2 (by linarith [h18.1.1])
  obtain ⟨C0, -, -, -, huniq, -⟩ := c4 0 ⟨by norm_num, by norm_num⟩
  have e1 : C = C0 := huniq C hC hr0 (by rw [hPhi0]; linarith)
  have e2 : D half = C0 := huniq _ hD c19 (by rw [c10, c19])
  rw [e1, e2]

theorem proof21 : obligation21 := by
  intro_premises
  refine ⟨fun _ => ⟨by norm_num, by norm_num, by norm_num⟩, fun x => ?_⟩
  unfold claim7 at c7
  have hz := c7 half x
  rw [coe_half] at hz
  have hx0 := x.2.1
  have hx1 := x.2.2
  unfold zeta
  rw [coe_half, hz]
  split_ifs with h1 h2 h3
  · have : (x : ℝ) = 0 := by linarith
    rw [this]; norm_num
  · have e : 2 * |(x : ℝ) + 1 / 2 - 1| = |2 * (x : ℝ) - 1| := by
      rw [← abs_two, ← abs_mul, abs_two]; ring_nf
    rw [e]
    exact coe_projIcc_of_mem (abs_bounds x).1 (abs_bounds x).2
  · exfalso
    apply h2
    rw [abs_le]
    constructor <;> norm_num <;> linarith
  · exfalso
    apply h2
    rw [abs_le]
    constructor <;> norm_num <;> linarith

theorem proof22 : obligation22 := by
  intro_premises
  have hD := m19.2.1
  refine ⟨⟨measurable_tentMap, ⟨by norm_num, by norm_num, by norm_num⟩, hD, by norm_num, by norm_num,
    by norm_num⟩, ?_⟩
  unfold claim21 at c21
  unfold claim22 supportedOnTheGraph
  intro u v
  simp only [D, copulaAssociatedWith, gamma, Leb, Prelude.leb]
  congr 1
  have hS : MeasurableSet {x : I | (x : ℝ) ≤ u ∧ ((tentMap x : I) : ℝ) ≤ v} :=
    (measurableSet_le measurable_subtype_coe measurable_const).inter
      (measurableSet_le (measurable_subtype_coe.comp measurable_tentMap) measurable_const)
  rw [← unitInterval.measurePreserving_symm.measure_preimage hS.nullMeasurableSet]
  congr 1
  ext t
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, unitInterval.coe_symm_eq, c21 t, tentMap]
  have ht0 := t.2.1
  have ht1 := t.2.2
  have hmin : min (2 * (1 - (t : ℝ))) (2 - 2 * (1 - (t : ℝ))) ≤ 1 := by
    rcases le_total (t : ℝ) (1 / 2) with h | h
    · exact min_le_of_right_le (by linarith)
    · exact min_le_of_left_le (by linarith)
  rw [coe_projIcc_of_mem (le_min (by linarith) (by linarith)) hmin]
  have e : 1 - |2 * (t : ℝ) - 1| = min (2 * (1 - (t : ℝ))) (2 - 2 * (1 - (t : ℝ))) := by
    rcases le_total (t : ℝ) (1 / 2) with h | h
    · rw [abs_of_nonpos (by linarith), min_eq_right (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith), min_eq_left (by linarith)]; ring
  rw [e]

theorem proof23 : obligation23 := by
  intro_premises
  unfold claim5 at c5
  unfold meaningful5 at m5
  refine ⟨fun C hC => ⟨⟨⟨hC, (m5 C hC).1.1.2.1, hC⟩, hC, (m5 C hC).1.1.2.1, hC⟩, hC, hC⟩, ?_⟩
  intro C hC
  obtain ⟨h1, h2, -⟩ := c5 C hC
  rw [h1, h2]
  ring

theorem proof24 : obligation24 := by
  intro_premises
  unfold claim10 at c10
  unfold claim18 at c18
  unfold claim19 at c19
  unfold claim20 at c20
  unfold claim23 at c23
  unfold meaningful5 at m5
  have hD := m19.2.1
  have hS : copulas (survival (D half)) := (m5 _ hD).1.1.2.1
  have hPhi0 : Phi 0 = 1 / 4 := (c18 0 ⟨by norm_num, by norm_num⟩).1.2
  have hgap : nu (D half) - rho (D half) = 1 / 4 := by rw [c10, c19, hPhi0]; norm_num
  have hh : (¬(2 : ℝ) = 0 ∧ (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1) := ⟨by norm_num, by norm_num, by norm_num⟩
  refine ⟨by unfold meaningful24; definedness [], ?_⟩
  refine ⟨⟨hS, by rw [c23 _ hD, ← neg_sub, hgap]⟩, fun C hC hmin => ?_⟩
  have hCS : copulas (survival C) := (m5 C hC).1.1.2.1
  have e : survival C = D half := c20 _ hCS (by rw [c23 C hC, ← neg_sub, hmin]; norm_num)
  rw [← survival_survival C, e]

theorem proof25 : obligation25 := by
  intro_premises
  unfold meaningful5 at m5
  unfold claim21 at c21
  have hD := m19.2.1
  have hS : copulas (survival (D half)) := (m5 _ hD).1.1.2.1
  have hh : (¬(2 : ℝ) = 0 ∧ (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1) := ⟨by norm_num, by norm_num, by norm_num⟩
  refine ⟨⟨abs_bounds, measurable_absMap, ⟨⟨hh, hD, hh⟩, hS, hh, hD, hh⟩, abs_bounds⟩, ?_⟩
  unfold claim25 supportedOnTheGraph
  intro u v
  set f : I → I := fun x => Set.projIcc (0 : ℝ) 1 zero_le_one |2 * (x : ℝ) - 1| with hf
  have hfv : ∀ x : I, (f x : ℝ) = |2 * (x : ℝ) - 1| := fun x =>
    coe_projIcc_of_mem (abs_bounds x).1 (abs_bounds x).2
  have hlaw : ∀ w : I, (volume : Measure I) {t | (f t : ℝ) ≤ w} = ENNReal.ofReal w := by
    intro w
    have h0 : (0 : ℝ) ≤ (1 - w) / 2 := by linarith [w.2.2]
    have h1 : (1 - (w : ℝ)) / 2 ≤ 1 := by linarith [w.2.1]
    have h2 : (0 : ℝ) ≤ (1 + w) / 2 := by linarith [w.2.1]
    have h3 : (1 + (w : ℝ)) / 2 ≤ 1 := by linarith [w.2.2]
    have : {t : I | (f t : ℝ) ≤ w} = Set.Icc ⟨(1 - w) / 2, h0, h1⟩ ⟨(1 + w) / 2, h2, h3⟩ := by
      ext t
      simp only [Set.mem_ofPred_eq, Set.mem_Icc, hfv, abs_le, ← Subtype.coe_le_coe]
      constructor
      · rintro ⟨a, b⟩; constructor <;> linarith
      · rintro ⟨a, b⟩; constructor <;> linarith
    rw [this, unitInterval.volume_Icc]
    congr 1
    ring
  have hnull : ∀ r : ℝ, (volume : Measure I) {t | (f t : ℝ) = r} = 0 := by
    intro r
    apply measure_mono_null (t := {t : I | (t : ℝ) = (1 - r) / 2} ∪ {t : I | (t : ℝ) = (1 + r) / 2})
    · intro t ht
      simp only [Set.mem_ofPred_eq, hfv] at ht
      rcases le_total (2 * (t : ℝ) - 1) 0 with h | h
      · rw [abs_of_nonpos h] at ht; left; show (t : ℝ) = _; linarith
      · rw [abs_of_nonneg h] at ht; right; show (t : ℝ) = _; linarith
    · exact measure_union_null (volume_level _) (volume_level _)
  have key := survival_graph f measurable_absMap hlaw hnull u v
  simp only [Leb, Prelude.leb]
  rw [← key]
  simp only [survival, D, copulaAssociatedWith, gamma, Prelude.leb, coe_reflect, c21]
  congr 3
  ext t
  simp only [Set.mem_ofPred_eq, hfv]
  constructor
  · rintro ⟨a, b⟩; constructor <;> linarith
  · rintro ⟨a, b⟩; constructor <;> linarith

/-! ## The statement, from the proof -/

/-- The bound `|ν(C) - ρ(C)| ≤ 1/4`, from Theorem 1.1 and the first sentences. -/
theorem gap_bounds (h3 : claim3) (h18 : claim18) (C : I → I → ℝ) (hC : copulas C) :
    -(1 / 4) ≤ nu C - rho C ∧ nu C - rho C ≤ 1 / 4 := by
  unfold claim3 at h3
  unfold claim18 at h18
  obtain ⟨⟨hr, -⟩, hlo, hup⟩ := (h3 (rho C) (nu C)).1 ⟨C, hC, rfl, rfl⟩
  have h := (h18 (rho C) hr).1
  constructor <;> linarith [h.1, h.2]

theorem proof11 : obligation11 := by
  intro_premises
  refine ⟨fun C hC => ⟨⟨hC, hC⟩, by norm_num⟩, fun C hC => ?_⟩
  exact abs_le.mpr (gap_bounds c3 c18 C hC)

theorem proof12 : obligation12 := by
  intro_premises
  have hD := m19.2.1
  unfold claim10 at c10
  unfold claim18 at c18
  unfold claim19 at c19
  have hPhi0 : Phi 0 = 1 / 4 := (c18 0 ⟨by norm_num, by norm_num⟩).1.2
  have hgap : nu (D half) - rho (D half) = 1 / 4 := by rw [c10, c19, hPhi0]; norm_num
  refine ⟨by unfold meaningful12; definedness [measurable_tentMap], ?_⟩
  exact ⟨⟨fun C hC => (gap_bounds c3 c18 C hC).2, ⟨hD, hgap⟩, c20⟩, c19, c22⟩

theorem proof13 : obligation13 := by
  intro_premises
  have hD := m19.2.1
  unfold meaningful5 at m5
  have hS : copulas (survival (D half)) := (m5 _ hD).1.1.2.1
  unfold claim24 at c24
  refine ⟨by unfold meaningful13; definedness [measurable_absMap, (abs_bounds _).2], ?_⟩
  exact ⟨⟨fun C hC => (gap_bounds c3 c18 C hC).1, c24.1, c24.2⟩, c25⟩

end Papers.Rockel2026ExactBlest.Source.Proofs
