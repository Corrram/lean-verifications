import Papers.Rockel2026ExactBlest.ExactBlestRegions

/-! Equality cases for exact-blest-regions.tex. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

/-- A deterministic graph and its uniform first marginal determine the copula. -/
theorem copula_eq_of_graph (C D : Copula 2) (f : I → I) (hf : Measurable f)
    (hc : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0))
    (hd : ∀ᵐ x ∂D.toMeasure, x 1 = f (x 0)) : C = D := by
  have hl (E : Copula 2) (he : ∀ᵐ x ∂E.toMeasure, x 1 = f (x 0)) :
      E.toMeasure = (volume : Measure I).map (fun u => ![u, f u]) := by
    have hm : Measurable (fun u : I => ![u, f u]) := by fun_prop
    rw [← E.map_eval 0, Measure.map_map hm (measurable_pi_apply 0)]
    have hv : (fun x : Fin 2 → I => ![x 0, f (x 0)]) =ᵐ[E.toMeasure] id := by
      filter_upwards [he] with x hx
      funext i
      fin_cases i
      · rfl
      · exact hx.symm
    change E.toMeasure = E.toMeasure.map (fun x => ![x 0, f (x 0)])
    rw [Measure.map_congr hv, Measure.map_id]
  apply Copula.ext
  rw [hl C hc, hl D hd]

def rhoRank (t u : I) : I :=
  ⟨if (u : ℝ) ≤ t then 2 * |(u : ℝ) - (t : ℝ) / 2| else (u : ℝ), by
    split_ifs with h
    · have ha : |(u : ℝ) - (t : ℝ) / 2| ≤ (t : ℝ) / 2 :=
        abs_le.mpr ⟨by linarith [u.property.1], by linarith⟩
      exact ⟨by positivity, by linarith [t.property.2]⟩
    · exact u.property⟩

theorem measurable_rhoRank (t : I) : Measurable (rhoRank t) := by
  apply Measurable.subtype_mk
  exact (show Measurable (fun u : I => 2 * |(u : ℝ) - (t : ℝ) / 2|) by fun_prop).ite
    (measurableSet_le measurable_subtype_coe measurable_const) measurable_subtype_coe

theorem rho_contact (t x z : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) (hz : 0 ≤ z)
    (heq : rhoParamPhi t x + rhoParamPsi t z - (x ^ 2 - t * x) * z = 0) :
    z = if x ≤ t then 2 * |x - t / 2| else x := by
  have hs : x ^ 2 - t * x = |x - t / 2| ^ 2 - t ^ 2 / 4 := by rw [sq_abs]; ring
  by_cases hxt : x ≤ t <;> by_cases hzt : z ≤ t
  · simp only [rhoParamPhi, rhoParamPsi, ite_eq_left hxt, ite_eq_left hzt] at heq ⊢
    have hid : (4 / 3) * |x - t / 2| ^ 3 + (z ^ 3 / 12 - t ^ 2 * z / 4) - (x ^ 2 - t * x) * z =
        (z - 2 * |x - t / 2|) ^ 2 * (z + 4 * |x - t / 2|) / 12 := by rw [hs]; ring
    rw [hid] at heq
    have hprod : (z - 2 * |x - t / 2|) ^ 2 * (z + 4 * |x - t / 2|) = 0 := by linarith
    by_cases hp : 0 < z + 4 * |x - t / 2|
    · have hsq := (mul_eq_zero.mp hprod).resolve_right hp.ne'
      have hzero := sq_eq_zero_iff.mp hsq
      linarith
    · linarith [abs_nonneg (x - t / 2)]
  · simp only [rhoParamPhi, rhoParamPsi, ite_eq_left hxt, ite_eq_right hzt] at heq ⊢
    have hq : 0 ≤ t ^ 2 / 4 - |x - t / 2| ^ 2 := by
      rw [sq_abs]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr hxt)]
    have hid : (4 / 3) * |x - t / 2| ^ 3 + (z ^ 3 / 3 - t * z ^ 2 / 2) - (x ^ 2 - t * x) * z =
        (t - 2 * |x - t / 2|) ^ 2 * (t + 4 * |x - t / 2|) / 12 +
        (t ^ 2 / 4 - |x - t / 2| ^ 2) * (z - t) + t / 2 * (z - t) ^ 2 + (z - t) ^ 3 / 3 := by
      rw [hs]; ring
    have hztp : 0 < z - t := by linarith
    have hpos : 0 < (t - 2 * |x - t / 2|) ^ 2 * (t + 4 * |x - t / 2|) / 12 +
        (t ^ 2 / 4 - |x - t / 2| ^ 2) * (z - t) + t / 2 * (z - t) ^ 2 + (z - t) ^ 3 / 3 := by positivity
    rw [hid] at heq
    linarith
  · simp only [rhoParamPhi, rhoParamPsi, ite_eq_right hxt, ite_eq_left hzt] at heq ⊢
    have hid : (2 * x ^ 3 / 3 - t * x ^ 2 / 2) + (z ^ 3 / 12 - t ^ 2 * z / 4) - (x ^ 2 - t * x) * z =
        (z - t) ^ 2 * (z + 2 * t) / 12 + t * (t - z) * (x - t) +
          (3 * t / 2 - z) * (x - t) ^ 2 + 2 * (x - t) ^ 3 / 3 := by ring
    have htz : 0 ≤ t - z := sub_nonneg.mpr hzt
    have hxtp : 0 < x - t := by linarith
    have hc : 0 ≤ 3 * t / 2 - z := by linarith
    have hpos : 0 < (z - t) ^ 2 * (z + 2 * t) / 12 + t * (t - z) * (x - t) +
        (3 * t / 2 - z) * (x - t) ^ 2 + 2 * (x - t) ^ 3 / 3 := by positivity
    rw [hid] at heq
    linarith
  · simp only [rhoParamPhi, rhoParamPsi, ite_eq_right hxt, ite_eq_right hzt] at heq ⊢
    have hid : (2 * x ^ 3 / 3 - t * x ^ 2 / 2) + (z ^ 3 / 3 - t * z ^ 2 / 2) - (x ^ 2 - t * x) * z =
        (x - z) ^ 2 * ((2 * x + z) / 3 - t / 2) := by ring
    rw [hid] at heq
    have hp : 0 < (2 * x + z) / 3 - t / 2 := by linarith
    have hsq := (mul_eq_zero.mp heq).resolve_right hp.ne'
    have hzero := sq_eq_zero_iff.mp hsq
    linarith

def rhoSlack (t : I) (x : Fin 2 → I) : ℝ :=
  rhoParamPhi t (x 0) + rhoParamPsi t (x 1) - ((x 0 : ℝ) ^ 2 - (t : ℝ) * (x 0 : ℝ)) * (x 1 : ℝ)

theorem rho_support_graph (C : Copula 2) (t : I)
    (hbound : blestNu C - (t : ℝ) * C.spearmanRho = 1 - (t : ℝ) + (t : ℝ) ^ 4 / 4) :
    ∀ᵐ x ∂C.survivalCopula.toMeasure, x 1 = rhoRank t (x 0) := by
  let D := C.survivalCopula
  have hp := integrable_rhoParamPhi D t 0
  have hq := integrable_rhoParamPsi D t 1
  have hi : Integrable (fun x : Fin 2 → I =>
      ((x 0 : ℝ) ^ 2 - (t : ℝ) * (x 0 : ℝ)) * (x 1 : ℝ)) D.toMeasure :=
    Copula.integrable_continuous_cube _ (by fun_prop)
  have hnon : 0 ≤ rhoSlack t := fun x => sub_nonneg.mpr
    (rho_param_dual t (x 0) (x 1) t.property.1 (x 0).property.1 (x 1).property.1)
  have hzero : (∫ x, rhoSlack t x ∂D.toMeasure) = 0 := by
    unfold rhoSlack
    have hsub := integral_sub (hp.add hq) hi
    simp only [Pi.add_apply] at hsub
    rw [hsub, integral_add hp hq,
      D.integral_eval 0 _ (measurable_rhoParamPhi t),
      D.integral_eval 1 _ (measurable_rhoParamPsi t), integral_rhoParamPhi, integral_rhoParamPsi]
    have hs := rho_support_moment C t
    rw [hbound] at hs
    change 1 - (t : ℝ) + (t : ℝ) ^ 4 / 4 =
      12 * (∫ x, ((x 0 : ℝ) ^ 2 - (t : ℝ) * (x 0 : ℝ)) * (x 1 : ℝ) ∂D.toMeasure) - 2 + 3 * (t : ℝ) at hs
    nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg hnon ((hp.add hq).sub hi)).mp hzero
  filter_upwards [hae] with x hx
  apply Subtype.ext
  exact rho_contact t (x 0) (x 1) t.property.1 (x 0).property.1 (x 1).property.1 hx

theorem rho_upper_graph (C : Copula 2) (t : I)
    (hr : C.spearmanRho = rhoPosR t) (hn : blestNu C = rhoPosN t) :
    ∀ᵐ x ∂C.survivalCopula.toMeasure, x 1 = rhoRank t (x 0) := by
  apply rho_support_graph C t
  rw [hr, hn]
  unfold rhoPosR rhoPosN
  ring

theorem rho_positive_unique (C D : Copula 2) (t : I)
    (hc : C.spearmanRho = rhoPosR t) (hnc : blestNu C = rhoPosN t)
    (hd : D.spearmanRho = rhoPosR t) (hnd : blestNu D = rhoPosN t) : C = D := by
  have h := copula_eq_of_graph C.survivalCopula D.survivalCopula (rhoRank t) (measurable_rhoRank t)
    (rho_upper_graph C t hc hnc) (rho_upper_graph D t hd hnd)
  have hs := congrArg Copula.survivalCopula h
  simpa only [Copula.survivalCopula_survivalCopula] using hs

#assert_standard_axioms Papers.Rockel2026ExactBlest.copula_eq_of_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.measurable_rhoRank
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_contact
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_support_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_upper_graph
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_positive_unique

theorem rho_support_unique (C D : Copula 2) (t : I)
    (hc : blestNu C - (t : ℝ) * C.spearmanRho = 1 - (t : ℝ) + (t : ℝ) ^ 4 / 4)
    (hd : blestNu D - (t : ℝ) * D.spearmanRho = 1 - (t : ℝ) + (t : ℝ) ^ 4 / 4) : C = D := by
  have h := copula_eq_of_graph C.survivalCopula D.survivalCopula (rhoRank t) (measurable_rhoRank t)
    (rho_support_graph C t hc) (rho_support_graph D t hd)
  have hs := congrArg Copula.survivalCopula h
  simpa only [Copula.survivalCopula_survivalCopula] using hs

theorem rho_upper_unique (C D : Copula 2) (hr : C.spearmanRho = D.spearmanRho)
    (hc : blestNu C = rhoBoundary C.spearmanRho) (hd : blestNu D = rhoBoundary D.spearmanRho) :
    C = D := by
  by_cases hp : 0 ≤ C.spearmanRho
  · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique C.spearmanRho ⟨hp, C.spearmanRho_mem_Icc.2⟩
    apply rho_positive_unique C D t ht.symm
    · rw [hc, ← ht, rhoBoundary_positive]
    · exact hr.symm.trans ht.symm
    · rw [hd, ← hr, ← ht, rhoBoundary_positive]
  · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique (-C.spearmanRho)
      ⟨by linarith, by linarith [C.spearmanRho_mem_Icc.1]⟩
    have he : C.spearmanRho = -rhoPosR t := by linarith
    apply Copula.reflect_injective {0}
    apply rho_positive_unique (C.reflect {0}) (D.reflect {0}) t
    · rw [Copula.spearmanRho_reflect_first, he]; ring
    · rw [nu_reflect_first, hc, he, rhoBoundary_negative]; ring
    · rw [Copula.spearmanRho_reflect_first, ← hr, he]; ring
    · rw [nu_reflect_first, hd, ← hr, he, rhoBoundary_negative]; ring

theorem rho_lower_unique (C D : Copula 2) (hr : C.spearmanRho = D.spearmanRho)
    (hc : blestNu C = 2 * C.spearmanRho - rhoBoundary C.spearmanRho)
    (hd : blestNu D = 2 * D.spearmanRho - rhoBoundary D.spearmanRho) : C = D := by
  have hs : C.survivalCopula = D.survivalCopula := by
    apply rho_upper_unique
    · simpa only [Copula.spearmanRho_survivalCopula] using hr
    · rw [nu_survival, Copula.spearmanRho_survivalCopula, hc]; ring
    · rw [nu_survival, Copula.spearmanRho_survivalCopula, hd]; ring
  simpa only [Copula.survivalCopula_survivalCopula] using congrArg Copula.survivalCopula hs

theorem rho_upper_exists_unique (r : ℝ) (hr : r ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, C.spearmanRho = r ∧ blestNu C = rhoBoundary r := by
  have hex : ∃ C : Copula 2, C.spearmanRho = r ∧ blestNu C = rhoBoundary r := by
    by_cases hp : 0 ≤ r
    · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique r ⟨hp, hr.2⟩
      refine ⟨rhoFamily t, (rho_family_values t).1.trans ht, ?_⟩
      rw [(rho_family_values t).2, ← ht, rhoBoundary_positive]
    · obtain ⟨t, ht, _⟩ := rho_parameter_exists_unique (-r) ⟨by linarith, by linarith [hr.1]⟩
      have he : r = -rhoPosR t := by linarith
      refine ⟨(rhoFamily t).reflect {0}, ?_, ?_⟩
      · rw [Copula.spearmanRho_reflect_first, (rho_family_values t).1, he]
      · rw [nu_reflect_first, (rho_family_values t).1, (rho_family_values t).2, he, rhoBoundary_negative]
  obtain ⟨C, hc, hn⟩ := hex
  refine ⟨C, ⟨hc, hn⟩, ?_⟩
  intro D hd
  exact rho_upper_unique D C (hd.1.trans hc.symm) (hd.2.trans (congrArg rhoBoundary hd.1.symm))
    (hn.trans (congrArg rhoBoundary hc.symm))

theorem rho_lower_exists_unique (r : ℝ) (hr : r ∈ Icc (-1 : ℝ) 1) :
    ∃! C : Copula 2, C.spearmanRho = r ∧ blestNu C = 2 * r - rhoBoundary r := by
  obtain ⟨C, hc, _⟩ := rho_upper_exists_unique r hr
  have hn : blestNu C.survivalCopula = 2 * r - rhoBoundary r := by
    rw [nu_survival, hc.1, hc.2]
  have hrC : C.survivalCopula.spearmanRho = r := (Copula.spearmanRho_survivalCopula C).trans hc.1
  refine ⟨C.survivalCopula, ⟨hrC, hn⟩, ?_⟩
  intro D hd
  apply rho_lower_unique D C.survivalCopula (hd.1.trans hrC.symm)
  · rw [hd.1]; exact hd.2
  · rw [hrC]; exact hn

theorem nu_rho_upper_unique (C D : Copula 2)
    (hc : blestNu C - C.spearmanRho = 1 / 4)
    (hd : blestNu D - D.spearmanRho = 1 / 4) : C = D := by
  apply rho_support_unique C D 1
  · simpa using hc
  · simpa using hd

theorem nu_rho_lower_unique (C D : Copula 2)
    (hc : blestNu C - C.spearmanRho = -1 / 4)
    (hd : blestNu D - D.spearmanRho = -1 / 4) : C = D := by
  have hs : C.survivalCopula = D.survivalCopula := by
    apply nu_rho_upper_unique
    · rw [nu_survival, Copula.spearmanRho_survivalCopula]; linarith
    · rw [nu_survival, Copula.spearmanRho_survivalCopula]; linarith
  simpa only [Copula.survivalCopula_survivalCopula] using congrArg Copula.survivalCopula hs

#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_support_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_lower_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_upper_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.rho_lower_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_rho_upper_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_rho_lower_unique

end
end Papers.Rockel2026ExactBlest
