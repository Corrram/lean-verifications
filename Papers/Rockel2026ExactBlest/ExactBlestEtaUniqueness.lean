import Papers.Rockel2026ExactBlest.ExactBlestUniqueness

/-! Equality cases for the eta/Blest region in exact-blest-regions.tex. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

/-- Uniform marginals put no mass on a specified coordinate line. -/
theorem ae_coord_ne (C : Copula 2) (i : Fin 2) (c : ℝ) :
    ∀ᵐ x ∂C.toMeasure, (x i : ℝ) ≠ c := by
  by_cases hc : c ∈ Icc (0 : ℝ) 1
  · let t : I := ⟨c, hc⟩
    have hz : C.toMeasure {x | x i = t} = 0 := by
      have hm := Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton t)
        (μ := C.toMeasure)
      rw [C.map_eval i] at hm
      simpa only [measure_singleton, Set.preimage, Set.mem_singleton_iff] using hm.symm
    have hae : ∀ᵐ x ∂C.toMeasure, x i ≠ t := by simpa only [ae_iff, not_not] using hz
    filter_upwards [hae] with x hx
    intro he
    exact hx (Subtype.ext he)
  · exact Filter.Eventually.of_forall (fun x h => hc (h ▸ (x i).property))

def graphRank (w u : I) : I :=
  ⟨if (u : ℝ) ≤ w then 1 - (u : ℝ) else (u : ℝ) - w, by
    split_ifs with h
    · constructor <;> linarith [u.property.1, u.property.2]
    · constructor <;> linarith [u.property.1, u.property.2, w.property.1]⟩

theorem measurable_graphRank (w : I) : Measurable (graphRank w) := by
  apply Measurable.subtype_mk
  exact (show Measurable (fun u : I => 1 - (u : ℝ)) by fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const) (by fun_prop)

/-- Off the two marginal-null cut lines, zero A-slack forces the graph. -/
theorem graph_contact (w x z : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (hxc : x ≠ w) (hzc : z ≠ 1 - w)
    (heq : phiA w x + psiA w z - cost (kA w) x z = 0) :
    z = if x ≤ w then 1 - x else x - w := by
  have hw : w ≠ 1 := by linarith
  have hden : 0 < 1 - w := by linarith
  have hw2 : 0 ≤ 1 - 2 * w := by linarith
  have hw5 : 0 < 5 - 2 * w := by linarith
  have hwx : 0 ≤ 1 + w - x := by linarith [hx.2]
  have hz0 := hz.1
  by_cases hxx : x ≤ w <;> by_cases hzz : z ≤ 1 - w
  · simp only [phiA, psiA, ite_eq_left hxx, ite_eq_left hzz] at heq
    rw [slackA00 w x z hw] at heq
    have hy : 0 < w - x := sub_pos.mpr (lt_of_le_of_ne hxx hxc)
    have ht : 0 ≤ 1 - w - z := by linarith
    have hp : 0 < w * z ^ 2 * (1 - w - z) / (1 - w) +
        ((1 - w - z) * ((1 - 2 * w) * (1 - w) + z * (2 * w + 1)) * (w - x) +
          (((1 - 2 * w) * (1 - w) + z * (2 * w + 1)) + (1 - w - z) * (5 - 2 * w)) *
            (w - x) ^ 2 / 2 + (5 - 2 * w) * (w - x) ^ 3 / 3) / (2 * (1 - w)) := by positivity
    linarith
  · simp only [phiA, psiA, ite_eq_left hxx, ite_eq_right hzz] at heq
    rw [slackA01 w x z hw] at heq
    have hy : 0 ≤ w - x := sub_nonneg.mpr hxx
    have ht : 0 < z - (1 - w) := by linarith
    have hp : 0 < 3 * (1 - w) + (5 - 2 * w) * (w - x) + (2 * w + 4) * (z - (1 - w)) := by positivity
    have hs := (mul_eq_zero.mp (((div_eq_zero_iff).mp heq).resolve_right (by positivity))).resolve_right hp.ne'
    have hh := sq_eq_zero_iff.mp hs
    rw [ite_eq_left hxx]
    linarith
  · simp only [phiA, psiA, ite_eq_right hxx, ite_eq_left hzz] at heq
    rw [slackA10 w x z hw] at heq
    have hy : 0 < x - w := by linarith
    have ht : 0 < 1 - w - z := by linarith [lt_of_le_of_ne hzz hzc]
    have hp : 0 < 2 * w * (1 - w - z) + (x - w) * (1 - 2 * w) := by
      by_cases hwz : w = 0
      · subst w; simpa using hy
      · have hwp : 0 < w := lt_of_le_of_ne hw0 (Ne.symm hwz)
        positivity
    have hs := (mul_eq_zero.mp (((div_eq_zero_iff).mp heq).resolve_right (by positivity))).resolve_right hp.ne'
    have hh := sq_eq_zero_iff.mp hs
    rw [ite_eq_right hxx]
    linarith
  · simp only [phiA, psiA, ite_eq_right hxx, ite_eq_right hzz] at heq
    rw [slackA11 w x z hw] at heq
    have hy : 0 < x - w := by linarith
    have ht : 0 < z - (1 - w) := by linarith
    have hp : 0 < (x - w) * (1 - 2 * w) * (1 - x) ^ 2 / (2 * (1 - w)) +
        ((x - w) * ((1 - w) * (1 + w - x)) * (z - (1 - w)) +
          ((1 - w) * (1 + w - x) + (x - w) * (w + 2)) * (z - (1 - w)) ^ 2 / 2 +
          (w + 2) * (z - (1 - w)) ^ 3 / 3) / (1 - w) := by positivity
    linarith

theorem graph_support_graph (C : Copula 2) (w : I) (hw : (w : ℝ) ≤ 1 / 2)
    (hbound : (1 + kA w) * blestNu C - 2 * kA w * eta C =
      (1 + kA w) * blestNu (familyA w) - 2 * kA w * eta (familyA w)) :
    ∀ᵐ x ∂C.survivalCopula.toMeasure, x 1 = graphRank w (x 0) := by
  let D := C.survivalCopula
  have hp := integrable_phiA D w 0
  have hq := integrable_psiA D w 1
  have hi : Integrable (fun x : Fin 2 → I => cost (kA w) (x 0) (x 1)) D.toMeasure :=
    Copula.integrable_continuous_cube _ (by unfold cost; fun_prop)
  let slack := fun x : Fin 2 → I => phiA w (x 0) + psiA w (x 1) - cost (kA w) (x 0) (x 1)
  have hnon : 0 ≤ slack := fun x => sub_nonneg.mpr
    (dualA w (x 0) (x 1) w.property.1 hw (x 0).property (x 1).property)
  have hzero : (∫ x, slack x ∂D.toMeasure) = 0 := by
    dsimp only [slack]
    have hsub := integral_sub (hp.add hq) hi
    simp only [Pi.add_apply] at hsub
    rw [hsub, integral_add hp hq, D.integral_eval 0 _ (measurable_phiA w),
      D.integral_eval 1 _ (measurable_psiA w), integral_potentialsA w hw]
    have hs := support_moment_survival C (kA w)
    rw [hbound] at hs
    change (1 + kA w) * blestNu (familyA w) - 2 * kA w * eta (familyA w) =
      12 * (∫ x, cost (kA w) (x 0) (x 1) ∂D.toMeasure) - 2 * (1 - kA w) at hs
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnon ((hp.add hq).sub hi)).mp hzero
  filter_upwards [hae, ae_coord_ne D 0 w, ae_coord_ne D 1 (1 - (w : ℝ))] with x hx hxc hzc
  apply Subtype.ext
  exact graph_contact w (x 0) (x 1) w.property.1 hw (x 0).property (x 1).property hxc hzc hx

theorem graph_support_unique (C : Copula 2) (w : I) (hw : (w : ℝ) ≤ 1 / 2)
    (hbound : (1 + kA w) * blestNu C - 2 * kA w * eta C =
      (1 + kA w) * blestNu (familyA w) - 2 * kA w * eta (familyA w)) : C = familyA w := by
  have h := copula_eq_of_graph C.survivalCopula (familyA w).survivalCopula (graphRank w)
    (measurable_graphRank w) (graph_support_graph C w hw hbound)
    (graph_support_graph (familyA w) w hw rfl)
  simpa only [Copula.survivalCopula_survivalCopula] using congrArg Copula.survivalCopula h

theorem graph_upper_unique (C : Copula 2) (w : I) (hw : (w : ℝ) ≤ 1 / 2)
    (he : eta C = eta (familyA w)) (hn : blestNu C = blestNu (familyA w)) : C = familyA w := by
  apply graph_support_unique C w hw
  rw [he, hn]

theorem graph_lower_unique (C : Copula 2) (w : I) (hw : (w : ℝ) ≤ 1 / 2)
    (he : eta C = eta (familyA w))
    (hn : blestNu C = 2 * eta (familyA w) - blestNu (familyA w)) : C = (familyA w).transpose := by
  have h : C.transpose = familyA w := by
    apply graph_upper_unique C.transpose w hw ((eta_transpose C).trans he)
    rw [nu_transpose, he, hn]
    ring
  simpa only [Copula.transpose_transpose] using congrArg Copula.transpose h

/-- The same graph-law argument with the second marginal as the parameter. -/
theorem copula_eq_of_reverse_graph (C D : Copula 2) (f : I → I) (hf : Measurable f)
    (hc : ∀ᵐ x ∂C.toMeasure, x 0 = f (x 1))
    (hd : ∀ᵐ x ∂D.toMeasure, x 0 = f (x 1)) : C = D := by
  have hl (E : Copula 2) (he : ∀ᵐ x ∂E.toMeasure, x 0 = f (x 1)) :
      E.toMeasure = (volume : Measure I).map (fun u => ![f u, u]) := by
    have hm : Measurable (fun u : I => ![f u, u]) := by fun_prop
    rw [← E.map_eval 1, Measure.map_map hm (measurable_pi_apply 1)]
    have hv : (fun x : Fin 2 → I => ![f (x 1), x 1]) =ᵐ[E.toMeasure] id := by
      filter_upwards [he] with x hx
      funext i
      fin_cases i
      · exact hx.symm
      · rfl
    change E.toMeasure = E.toMeasure.map (fun x => ![f (x 1), x 1])
    rw [Measure.map_congr hv, Measure.map_id]
  apply Copula.ext
  rw [hl C hc, hl D hd]

def randomRankReal (a z : ℝ) : ℝ :=
  if z ≤ cutB a then 2 * a * z + a
  else if z ≤ 1 - a then a * (1 - 2 * z) / (2 * a - 1) else 1 - z

theorem randomRankReal_mem (a z : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1)
    (hz : z ∈ Icc (0 : ℝ) 1) : randomRankReal a z ∈ Icc (0 : ℝ) 1 := by
  have ha0 : 0 < a := by linarith
  have ha2 : 0 < 2 * a - 1 := by linarith
  unfold randomRankReal
  split_ifs with hc hm
  · have ht := (le_div_iff₀ (by positivity : 0 < 2 * a)).mp hc
    exact ⟨by nlinarith [hz.1], by nlinarith⟩
  · have ht := (div_lt_iff₀ (by positivity : 0 < 2 * a)).mp (lt_of_not_ge hc)
    constructor
    · apply div_nonneg _ ha2.le
      have h : 0 ≤ 1 - 2 * z := by linarith
      positivity
    · apply (div_le_iff₀ ha2).mpr
      nlinarith
  · constructor <;> linarith [hz.1, hz.2]

def randomRank (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) (z : I) : I :=
  ⟨randomRankReal a z, randomRankReal_mem a z ha ha1 z.property⟩

theorem measurable_randomRank (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    Measurable (randomRank a ha ha1) := by
  apply Measurable.subtype_mk
  unfold randomRankReal
  exact (show Measurable (fun z : I => 2 * a * (z : ℝ) + a) by fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const)
    ((show Measurable (fun z : I => a * (1 - 2 * (z : ℝ)) / (2 * a - 1)) by fun_prop).ite
      (measurableSet_le measurable_subtype_coe measurable_const) (by fun_prop))

/-- Zero B-slack determines X from Z away from marginal-null cut lines. -/
theorem randomized_contact (a x z : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1)
    (hx : x ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 1)
    (hxc : x ≠ a) (hzc : z ≠ cutB a)
    (heq : phiB a x + psiB a z - cost (kB a) x z = 0) : x = randomRankReal a z := by
  have ha0 : 0 < a := by linarith
  have hn0 : a ≠ 0 := ha0.ne'
  have hn1 : a ≠ 1 := ha1.ne
  have ha2 : 0 < 2 * a - 1 := by linarith
  have hn2 := ha2.ne'
  have ha3 : 0 < 3 * a - 1 := by linarith
  have hden : 0 < 1 - a := by linarith
  have hxa : 0 ≤ 1 - x := by linarith [hx.2]
  have hz0 := hz.1
  have hcut : cutB a ≤ 1 - a := by
    unfold cutB
    apply (div_le_iff₀ (by positivity : 0 < 2 * a)).2
    nlinarith [mul_nonneg hden.le ha2.le]
  unfold phiB psiB at heq
  unfold randomRankReal
  by_cases hxx : x ≤ a
  · rw [ite_eq_left hxx] at heq
    have hy : 0 < a - x := sub_pos.mpr (lt_of_le_of_ne hxx hxc)
    by_cases hc : z ≤ cutB a
    · rw [ite_eq_left hc, slackB00 a x z hn1] at heq
      have ht : 0 ≤ 1 - a - z := by linarith
      have hr : 0 ≤ 1 - a - 2 * a * z := by
        have := (le_div_iff₀ (by positivity : 0 < 2 * a)).mp hc
        nlinarith
      have hp : 0 < 2 * a * z ^ 2 * ((1 - a) * (2 * a - 1) + (1 + a) * (1 - a - 2 * a * z)) /
          (3 * (1 - a)) + 2 * ((1 - a - z) * a * z * (a - x) +
          (1 - a - z + a * z) * (a - x) ^ 2 / 2 + (a - x) ^ 3 / 3) / (1 - a) := by positivity
      linarith
    · rw [ite_eq_right hc] at heq ⊢
      by_cases hm : z ≤ 1 - a
      · rw [ite_eq_left hm, slackB01 a x z hn0 hn1 hn2] at heq
        have ht : 0 ≤ 1 - a - z := by linarith
        have hr : 0 ≤ 2 * a * z - (1 - a) := by
          have := (div_lt_iff₀ (by positivity : 0 < 2 * a)).mp (lt_of_not_ge hc)
          nlinarith
        have hp : 0 < 2 * a * (1 - a - z) ^ 2 *
            ((1 - a) * (2 * a - 1) + (3 * a - 1) * (2 * a * z - (1 - a))) /
            (3 * (1 - a) * (2 * a - 1) ^ 2) +
            2 * ((1 - a - z) * a * z * (a - x) +
            (1 - a - z + a * z) * (a - x) ^ 2 / 2 + (a - x) ^ 3 / 3) / (1 - a) := by positivity
        linarith
      · rw [ite_eq_right hm, slackB02 a x z hn0 hn1 hn2] at heq
        rw [ite_eq_right hm]
        have ht : 0 < z - (1 - a) := by linarith
        have hp : 0 < 3 * a * (1 - a) + 2 * (a - x) + (3 * a + 1) * (z - (1 - a)) := by positivity
        have hs := (mul_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right (by positivity))).resolve_right hp.ne'
        have hh := sq_eq_zero_iff.mp hs
        linarith
  · rw [ite_eq_right hxx] at heq
    have hy : 0 < x - a := by linarith
    by_cases hc : z ≤ cutB a
    · rw [ite_eq_left hc, slackB10 a x z hn0 hn1] at heq
      rw [ite_eq_left hc]
      have hr : 0 < 1 - a - 2 * a * z := by
        have := (lt_div_iff₀ (by positivity : 0 < 2 * a)).mp (lt_of_le_of_ne hc hzc)
        nlinarith
      have hp : 0 < (2 * a - 1) * (1 - x) + (1 + a) * (1 - a - 2 * a * z) := by positivity
      have hs := (mul_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right (by positivity))).resolve_right hp.ne'
      have hh := sq_eq_zero_iff.mp hs
      linarith
    · rw [ite_eq_right hc] at heq ⊢
      by_cases hm : z ≤ 1 - a
      · rw [ite_eq_left hm, slackB11 a x z hn0 hn1 hn2] at heq
        rw [ite_eq_left hm]
        have hr : 0 < 2 * a * z - (1 - a) := by
          have := (div_lt_iff₀ (by positivity : 0 < 2 * a)).mp (lt_of_not_ge hc)
          nlinarith
        have hp : 0 < (2 * a - 1) * (1 - x) + (3 * a - 1) * (2 * a * z - (1 - a)) := by positivity
        have hs := (mul_eq_zero.mp ((div_eq_zero_iff.mp heq).resolve_right (by positivity))).resolve_right hp.ne'
        have hh := sq_eq_zero_iff.mp hs
        apply (eq_div_iff hn2).mpr
        nlinarith
      · rw [ite_eq_right hm, slackB12 a x z hn0 hn1 hn2] at heq
        have ht : 0 < z - (1 - a) := by linarith
        have hr : 0 ≤ 2 * a * z - (x - a) := by
          nlinarith [mul_nonneg ha2.le hden.le, mul_nonneg ha0.le ht.le, hx.2]
        have hp : 0 < (z - (1 - a)) ^ 2 * (3 * a * (1 - a) + (3 * a + 1) * (z - (1 - a))) /
            (3 * (1 - a)) +
            ((2 * a * z - (x - a)) * (2 * a * (z - (1 - a))) * (x - a) +
            (2 * a * (z - (1 - a)) + (2 * a * z - (x - a)) * (2 * a - 1)) * (x - a) ^ 2 / 2 +
            (2 * a - 1) * (x - a) ^ 3 / 6) / (2 * a * (1 - a)) := by positivity
        linarith

theorem randomized_support_graph (C : Copula 2) (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1)
    (hbound : (1 + kB a) * blestNu C - 2 * kB a * eta C =
      (1 + kB a) * nuB a - 2 * kB a * etaB a) :
    ∀ᵐ x ∂C.survivalCopula.toMeasure, x 0 = randomRank a ha ha1 (x 1) := by
  let D := C.survivalCopula
  have hp := integrable_phiB D a 0
  have hq := integrable_psiB D a 1
  have hi : Integrable (fun x : Fin 2 → I => cost (kB a) (x 0) (x 1)) D.toMeasure :=
    Copula.integrable_continuous_cube _ (by unfold cost; fun_prop)
  let slack := fun x : Fin 2 → I => phiB a (x 0) + psiB a (x 1) - cost (kB a) (x 0) (x 1)
  have hnon : 0 ≤ slack := fun x => sub_nonneg.mpr
    (dualB a (x 0) (x 1) ha ha1 (x 0).property (x 1).property)
  have hzero : (∫ x, slack x ∂D.toMeasure) = 0 := by
    dsimp only [slack]
    have hsub := integral_sub (hp.add hq) hi
    simp only [Pi.add_apply] at hsub
    rw [hsub, integral_add hp hq, D.integral_eval 0 _ (measurable_phiB a),
      D.integral_eval 1 _ (measurable_psiB a), integral_potentialsB a ha ha1]
    have hs := support_moment_survival C (kB a)
    rw [hbound] at hs
    change (1 + kB a) * nuB a - 2 * kB a * etaB a =
      12 * (∫ x, cost (kB a) (x 0) (x 1) ∂D.toMeasure) - 2 * (1 - kB a) at hs
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg hnon ((hp.add hq).sub hi)).mp hzero
  filter_upwards [hae, ae_coord_ne D 0 a, ae_coord_ne D 1 (cutB a)] with x hx hxc hzc
  apply Subtype.ext
  exact randomized_contact a (x 0) (x 1) ha ha1 (x 0).property (x 1).property hxc hzc hx

theorem randomized_support_unique (C : Copula 2) (a : I) (ha : 1 / 2 < (a : ℝ)) (ha1 : (a : ℝ) < 1)
    (hbound : (1 + kB a) * blestNu C - 2 * kB a * eta C =
      (1 + kB a) * nuB a - 2 * kB a * etaB a) : C = familyB a ha.le := by
  have hd : (1 + kB a) * blestNu (familyB a ha.le) - 2 * kB a * eta (familyB a ha.le) =
      (1 + kB a) * nuB a - 2 * kB a * etaB a := by rw [nu_familyB, eta_familyB]
  have h := copula_eq_of_reverse_graph C.survivalCopula (familyB a ha.le).survivalCopula
    (randomRank a ha ha1) (measurable_randomRank a ha ha1)
    (randomized_support_graph C a ha ha1 hbound) (randomized_support_graph (familyB a ha.le) a ha ha1 hd)
  simpa only [Copula.survivalCopula_survivalCopula] using congrArg Copula.survivalCopula h

theorem randomized_upper_unique (C : Copula 2) (a : I) (ha : 1 / 2 < (a : ℝ)) (ha1 : (a : ℝ) < 1)
    (he : eta C = etaB a) (hn : blestNu C = nuB a) : C = familyB a ha.le := by
  apply randomized_support_unique C a ha ha1
  rw [he, hn]

theorem randomized_lower_unique (C : Copula 2) (a : I) (ha : 1 / 2 < (a : ℝ)) (ha1 : (a : ℝ) < 1)
    (he : eta C = etaB a) (hn : blestNu C = 2 * etaB a - nuB a) : C = (familyB a ha.le).transpose := by
  have h : C.transpose = familyB a ha.le := by
    apply randomized_upper_unique C.transpose a ha ha1 ((eta_transpose C).trans he)
    rw [nu_transpose, he, hn]
    ring
  simpa only [Copula.transpose_transpose] using congrArg Copula.transpose h

theorem blest_max_unique (C D : Copula 2) (hc : blestNu C = 1) (hd : blestNu D = 1) : C = D := by
  apply rho_support_unique C D 0
  · simpa using hc
  · simpa using hd

theorem blest_min_unique (C D : Copula 2) (hc : blestNu C = -1) (hd : blestNu D = -1) : C = D := by
  apply Copula.reflect_injective {1}
  apply blest_max_unique
  · rw [blest_reflect_second, hc]; norm_num
  · rw [blest_reflect_second, hd]; norm_num

theorem eta_bottom_unique (C D : Copula 2) (hc : eta C = -1) (hd : eta D = -1) : C = D := by
  exact blest_min_unique C D ((eta_bottom_fibre _).mp ⟨C, hc, rfl⟩)
    ((eta_bottom_fibre _).mp ⟨D, hd, rfl⟩)

/-- Unique upper-boundary copula at every eta, including both junctions. -/
theorem eta_upper_unique (C D : Copula 2) (he : eta C = eta D)
    (hc : blestNu C = eta C + etaGap (eta C))
    (hd : blestNu D = eta D + etaGap (eta D)) : C = D := by
  by_cases hg : -3 / 4 ≤ eta C
  · obtain ⟨w, hw, _⟩ := graph_parameter_exists_unique (eta C) ⟨hg, (eta_mem_Icc C).2⟩
    have hnc : blestNu C = blestNu (familyA w) := by
      rw [hc, ← hw.2, etaGap_graph w hw.1]; ring
    have hnd : blestNu D = blestNu (familyA w) := by
      rw [hd, ← he, ← hw.2, etaGap_graph w hw.1]; ring
    exact (graph_upper_unique C w hw.1 hw.2.symm hnc).trans
      (graph_upper_unique D w hw.1 (he.symm.trans hw.2.symm) hnd).symm
  · by_cases hb : eta C = -1
    · exact eta_bottom_unique C D hb (he.symm.trans hb)
    · obtain ⟨a, ha, ha1, hav⟩ := randomized_parameter_exists_open (eta C)
        ⟨lt_of_le_of_ne (eta_mem_Icc C).1 (Ne.symm hb), by linarith⟩
      have hnc : blestNu C = nuB a := by rw [hc, ← hav, etaGap_randomized a ha]; ring
      have hnd : blestNu D = nuB a := by rw [hd, ← he, ← hav, etaGap_randomized a ha]; ring
      exact (randomized_upper_unique C a ha ha1 hav.symm hnc).trans
        (randomized_upper_unique D a ha ha1 (he.symm.trans hav.symm) hnd).symm

theorem eta_lower_unique (C D : Copula 2) (he : eta C = eta D)
    (hc : blestNu C = eta C - etaGap (eta C))
    (hd : blestNu D = eta D - etaGap (eta D)) : C = D := by
  have h : C.transpose = D.transpose := by
    apply eta_upper_unique
    · simpa only [eta_transpose] using he
    · rw [eta_transpose, nu_transpose, hc]; ring
    · rw [eta_transpose, nu_transpose, hd]; ring
  simpa only [Copula.transpose_transpose] using congrArg Copula.transpose h

theorem eta_upper_exists_unique (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, eta C = e ∧ blestNu C = e + etaGap e := by
  have hex : ∃ C : Copula 2, eta C = e ∧ blestNu C = e + etaGap e := by
    by_cases hg : -3 / 4 ≤ e
    · obtain ⟨w, hw, _⟩ := graph_parameter_exists_unique e ⟨hg, he.2⟩
      refine ⟨familyA w, hw.2, ?_⟩
      rw [← hw.2, etaGap_graph w hw.1]; ring
    · by_cases hb : e = -1
      · subst e
        refine ⟨familyA 1, ?_, ?_⟩
        · rw [eta_familyA]; norm_num
        · rw [nu_familyA, etaGap_bottom]; norm_num
      · obtain ⟨a, ha, _, hav⟩ := randomized_parameter_exists_open e
          ⟨lt_of_le_of_ne he.1 (Ne.symm hb), by linarith⟩
        refine ⟨familyB a ha.le, (eta_familyB a ha.le).trans hav, ?_⟩
        rw [nu_familyB, ← hav, etaGap_randomized a ha]; ring
  obtain ⟨C, hc, hn⟩ := hex
  refine ⟨C, ⟨hc, hn⟩, ?_⟩
  intro D hd
  apply eta_upper_unique D C (hd.1.trans hc.symm)
  · rw [hd.1]; exact hd.2
  · rw [hc]; exact hn

theorem eta_lower_exists_unique (e : ℝ) (he : e ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, eta C = e ∧ blestNu C = e - etaGap e := by
  obtain ⟨C, hc, _⟩ := eta_upper_exists_unique e he
  have heC : eta C.transpose = e := (eta_transpose C).trans hc.1
  have hn : blestNu C.transpose = e - etaGap e := by rw [nu_transpose, hc.1, hc.2]; ring
  refine ⟨C.transpose, ⟨heC, hn⟩, ?_⟩
  intro D hd
  apply eta_lower_unique D C.transpose (hd.1.trans heC.symm)
  · rw [hd.1]; exact hd.2
  · rw [heC]; exact hn

/-- The sharp asymmetry equality singles out the quarter-parameter copula. -/
theorem asymmetry_upper_unique (C : Copula 2) (hc : blestNu C - eta C = 27 / 128) :
    C = familyA quarter := by
  apply graph_support_unique C quarter (by norm_num [quarter])
  have hk : kA quarter = 1 := by norm_num [kA, quarter]
  rw [hk, quarter_values.1, quarter_values.2]
  linarith

theorem asymmetry_lower_unique (C : Copula 2) (hc : blestNu C - eta C = -27 / 128) :
    C = (familyA quarter).transpose := by
  have h : C.transpose = familyA quarter := by
    apply asymmetry_upper_unique
    rw [nu_transpose, eta_transpose]; linarith
  simpa only [Copula.transpose_transpose] using congrArg Copula.transpose h

theorem asymmetry_eq_iff (C : Copula 2) :
    |blestNu C - eta C| = 27 / 128 ↔ C = familyA quarter ∨ C = (familyA quarter).transpose := by
  constructor
  · intro h
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 27 / 128)).mp h with hp | hn
    · exact Or.inl (asymmetry_upper_unique C hp)
    · exact Or.inr (asymmetry_lower_unique C (by linarith))
  · rintro (rfl | rfl)
    · rw [quarter_values.1, quarter_values.2]; norm_num
    · rw [nu_transpose, eta_transpose, quarter_values.1, quarter_values.2]; norm_num

theorem transposition_eq_iff (C : Copula 2) :
    |blestNu C - blestNu C.transpose| = 27 / 64 ↔
      C = familyA quarter ∨ C = (familyA quarter).transpose := by
  rw [← asymmetry_eq_iff, asymmetry_identity]
  constructor <;> intro h <;> linarith

theorem rho_eta_upper_unique (C : Copula 2) (hc : C.spearmanRho - eta C = 27 / 128) :
    C = (familyA quarter).reflect {1} := by
  have h : C.reflect {1} = familyA quarter :=
    asymmetry_upper_unique _ ((reflection_byproduct C).trans hc)
  simpa only [Copula.reflect_reflect] using congrArg (fun E : Copula 2 => E.reflect {1}) h

theorem rho_eta_lower_unique (C : Copula 2) (hc : C.spearmanRho - eta C = -27 / 128) :
    C = (familyA quarter).transpose.reflect {1} := by
  have h : C.reflect {1} = (familyA quarter).transpose :=
    asymmetry_lower_unique _ ((reflection_byproduct C).trans hc)
  simpa only [Copula.reflect_reflect] using congrArg (fun E : Copula 2 => E.reflect {1}) h

/-- The reflected-coordinate law really is the paper's graph coupling. -/
theorem familyA_graph_law (w : I) (hw : (w : ℝ) ≤ 1 / 2) :
    (familyA w).survivalCopula.toMeasure = (volume : Measure I).map (fun u => ![u, graphRank w u]) := by
  let E := (familyA w).survivalCopula
  have hm : Measurable (fun u : I => ![u, graphRank w u]) := by
    have := measurable_graphRank w
    fun_prop
  rw [← E.map_eval 0, Measure.map_map hm (measurable_pi_apply 0)]
  have hv : (fun x : Fin 2 → I => ![x 0, graphRank w (x 0)]) =ᵐ[E.toMeasure] id := by
    filter_upwards [graph_support_graph (familyA w) w hw rfl] with x hx
    funext i
    fin_cases i
    · rfl
    · exact hx.symm
  change E.toMeasure = E.toMeasure.map (fun x => ![x 0, graphRank w (x 0)])
  rw [Measure.map_congr hv, Measure.map_id]

theorem familyB_graph_law (a : I) (ha : 1 / 2 < (a : ℝ)) (ha1 : (a : ℝ) < 1) :
    (familyB a ha.le).survivalCopula.toMeasure =
      (volume : Measure I).map (fun z => ![randomRank a ha ha1 z, z]) := by
  let E := (familyB a ha.le).survivalCopula
  have hm : Measurable (fun z : I => ![randomRank a ha ha1 z, z]) := by
    have := measurable_randomRank a ha ha1
    fun_prop
  rw [← E.map_eval 1, Measure.map_map hm (measurable_pi_apply 1)]
  have hb : (1 + kB a) * blestNu (familyB a ha.le) - 2 * kB a * eta (familyB a ha.le) =
      (1 + kB a) * nuB a - 2 * kB a * etaB a := by rw [nu_familyB, eta_familyB]
  have hv : (fun x : Fin 2 → I => ![randomRank a ha ha1 (x 1), x 1]) =ᵐ[E.toMeasure] id := by
    filter_upwards [randomized_support_graph (familyB a ha.le) a ha ha1 hb] with x hx
    funext i
    fin_cases i
    · exact hx.symm
    · rfl
  change E.toMeasure = E.toMeasure.map (fun x => ![randomRank a ha ha1 (x 1), x 1])
  rw [Measure.map_congr hv, Measure.map_id]

theorem familyB_half : familyB Copula.unitHalf (by norm_num [Copula.unitHalf]) = familyA Copula.unitHalf := by
  apply graph_upper_unique _ Copula.unitHalf (by norm_num [Copula.unitHalf])
  · rw [eta_familyB, eta_familyA]; norm_num [Copula.unitHalf, etaB]
  · rw [nu_familyB, nu_familyA]; norm_num [Copula.unitHalf, nuB]

theorem familyA_zero : familyA 0 = Copula.comonotonic 2 := by
  apply blest_max_unique
  · rw [nu_familyA]; norm_num
  · exact blest_comonotonic

theorem familyA_one : familyA 1 = Copula.countermonotonic := by
  apply blest_min_unique
  · rw [nu_familyA]; norm_num
  · exact blest_countermonotonic

theorem familyB_one : familyB 1 (by norm_num) = Copula.countermonotonic := by
  apply blest_min_unique
  · rw [nu_familyB]; norm_num [nuB]
  · exact blest_countermonotonic

/-- Monotonicity on the entire A-family, not just its boundary subfamily. -/
theorem eta_familyA_strictAnti : StrictAnti (fun w : I => eta (familyA w)) := by
  intro x y hxy
  have hxy' : (x : ℝ) < y := hxy
  have hp : (1 - (y : ℝ)) ^ 3 < (1 - (x : ℝ)) ^ 3 := by
    gcongr
    linarith [y.property.2]
  change eta (familyA y) < eta (familyA x)
  rw [eta_familyA, eta_familyA]
  linarith

#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyB_graph_law
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyB_half
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_zero
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyA_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.familyB_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_familyA_strictAnti

#assert_standard_axioms Papers.Rockel2026ExactBlest.blest_max_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.blest_min_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_bottom_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_lower_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_upper_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.eta_lower_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.asymmetry_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.asymmetry_lower_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.asymmetry_eq_iff
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposition_eq_iff
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_eta_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_eta_lower_unique

#assert_standard_axioms Papers.Rockel2026ExactBlest.copula_eq_of_reverse_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomRankReal_mem
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_randomRank
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_contact
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_support_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_support_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.randomized_lower_unique

#assert_standard_axioms Papers.Rockel2026ExactBlest.ae_coord_ne
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_graphRank
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_contact
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_support_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_support_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.graph_lower_unique

end
end Papers.Rockel2026ExactBlest
