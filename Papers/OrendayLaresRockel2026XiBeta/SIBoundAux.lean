import Papers.OrendayLaresRockel2026XiBeta.CompletionXi

/-! # An Abel-type lemma for nonincreasing weights

If `h : [0,1] → [0,1]` is nonincreasing and all partial integrals `∫_{[0,u]} f` are
nonnegative, then `∫ h f ≥ 0`.  This is the layer-cake/Fubini step in the proof of Lemma 5.1 (iii).
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The integral of `f` over a lower set of `[0,1]` is nonnegative if all partial integrals are. -/
theorem integral_lowerSet_nonneg {S : Set I} (hS : IsLowerSet S) {f : I → ℝ}
    (hpart : ∀ u : I, 0 ≤ ∫ t in Iic u, f t) : 0 ≤ ∫ t in S, f t := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · set x := sSup S with hx
    have hIio : Iio x ⊆ S := fun y hy => by
      obtain ⟨a, ha, hya⟩ := exists_lt_of_lt_csSup hne hy
      exact hS hya.le ha
    have hae : S =ᵐ[volume] Iic x := by
      have hn : ∀ᵐ y : I, y ∉ ({x} : Set I) := (Set.countable_singleton x).ae_notMem volume
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [hn] with y hy
      constructor
      · intro hyS; exact le_csSup (OrderTop.bddAbove S) hyS
      · intro hyx
        have : y < x := lt_of_le_of_ne hyx (by simpa using hy)
        exact hIio this
    rw [setIntegral_congr_set hae]
    exact hpart x

theorem integral_antitone_mul_nonneg {h f : I → ℝ} (hh : Antitone h)
    (hb : ∀ u, h u ∈ Icc (0 : ℝ) 1) (hfm : Measurable f) (hfb : ∀ u, |f u| ≤ 1)
    (hpart : ∀ u : I, 0 ≤ ∫ t in Iic u, f t) : 0 ≤ ∫ u, h u * f u := by
  classical
  have hlayer : ∀ u, h u = ∫ τ : I, (if (τ : ℝ) < h u then (1 : ℝ) else 0) := by
    intro u
    rw [Copula.integral_unitInterval (fun τ => if τ < h u then (1 : ℝ) else 0)]
    have hm : ∀ a b : ℝ, IntervalIntegrable (fun τ : ℝ => if τ < h u then (1 : ℝ) else 0)
        volume a b := by
      intro a b
      have : Measurable (fun τ : ℝ => if τ < h u then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
          measurable_const
      refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' this.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x < h u <;> simp [hx])
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := h u) (hm _ _) (hm _ _),
      integral_eq_of_eq_on_Ioo (hb u).1 (k := 1) (fun t ht => by simp [ht.2]),
      integral_eq_of_eq_on_Ioo (hb u).2 (k := 0) (fun t ht => by
        have : ¬ t < h u := not_lt.mpr ht.1.le
        simp [this])]
    ring
  have hset : ∀ τ : I, MeasurableSet {u : I | (τ : ℝ) < h u} :=
    fun τ => measurableSet_lt measurable_const hh.measurable
  have hint : Integrable (Function.uncurry fun (u τ : I) =>
      (if (τ : ℝ) < h u then (1 : ℝ) else 0) * f u) (volume.prod volume) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · have h1 : Measurable (fun z : I × I => if ((z.2 : I) : ℝ) < h z.1 then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_lt (measurable_subtype_coe.comp measurable_snd)
          (hh.measurable.comp measurable_fst)) measurable_const measurable_const
      exact (h1.mul (hfm.comp measurable_fst)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun z => ?_)
      simp only [Function.uncurry, Real.norm_eq_abs]
      by_cases hz : ((z.2 : I) : ℝ) < h z.1
      · simpa [hz] using hfb z.1
      · simp [hz]
  have hswap := integral_integral_swap (μ := (volume : Measure I)) (ν := (volume : Measure I)) hint
  calc (0 : ℝ) ≤ ∫ τ : I, ∫ u : I, (if (τ : ℝ) < h u then (1 : ℝ) else 0) * f u := by
        refine integral_nonneg (fun τ => ?_)
        show 0 ≤ ∫ u : I, (if (τ : ℝ) < h u then (1 : ℝ) else 0) * f u
        have e : (fun u : I => (if (τ : ℝ) < h u then (1 : ℝ) else 0) * f u) =
            {u : I | (τ : ℝ) < h u}.indicator f := by
          funext u
          by_cases hu : (τ : ℝ) < h u <;> simp [hu, Set.indicator]
        rw [e, integral_indicator (hset τ)]
        apply integral_lowerSet_nonneg _ hpart
        intro a b hab ha
        exact lt_of_lt_of_le ha (hh hab)
    _ = ∫ u : I, ∫ τ : I, (if (τ : ℝ) < h u then (1 : ℝ) else 0) * f u := hswap.symm
    _ = ∫ u : I, h u * f u := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun u => ?_)
        simp only
        rw [integral_mul_const, ← hlayer u]

end Papers.OrendayLaresRockel2026XiBeta
