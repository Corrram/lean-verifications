import Papers.Rockel2026ExactBlest.ExactBlestBetaUniqueness
import Copula.Distribution.ProbabilityIntegralTransform

/-! The general integrable rearrangement lemma from exact-blest-regions.tex. -/
open MeasureTheory ProbabilityTheory Set
open scoped unitInterval Topology
namespace Papers.Rockel2026ExactBlest
noncomputable section
set_option maxHeartbeats 4000000

def tailIndicator (v t : I) : ℝ := if t < v then 1 else 0

theorem integral_tailIndicator (v : I) : (∫ t : I, tailIndicator v t) = (v : ℝ) := by
  have he : (fun t : I => tailIndicator v t) = (Iio v).indicator (fun _ => (1 : ℝ)) := by
    ext t
    simp [tailIndicator, Set.indicator]
  rw [he, integral_indicator_const (1 : ℝ) measurableSet_Iio]
  simp [Measure.real, v.property.1]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_uniform_tail (V : Ω → I) (hV : MeasurePreserving V μ volume) (t : I) :
    (∫ ω, tailIndicator (V ω) t ∂μ) = 1 - (t : ℝ) := by
  have hm : Measurable (fun v : I => tailIndicator v t) :=
    measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const
  have he : (fun v : I => tailIndicator v t) = (Ioi t).indicator (fun _ => (1 : ℝ)) := by
    ext v
    simp [tailIndicator, Set.indicator]
  rw [← integral_map hV.measurable.aemeasurable hm.aestronglyMeasurable, hV.map_eq,
    he, integral_indicator_const (1 : ℝ) measurableSet_Ioi]
  simp [Measure.real, sub_nonneg.mpr t.property.2]

theorem uniform_ae_ne (V : Ω → I) (hV : MeasurePreserving V μ volume) (t : I) :
    ∀ᵐ ω ∂μ, V ω ≠ t := by
  have hm := Measure.map_apply hV.measurable (measurableSet_singleton t) (μ := μ)
  rw [hV.map_eq, measure_singleton] at hm
  have hz : μ {ω | V ω = t} = 0 := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using hm.symm
  simpa only [ae_iff, not_not] using hz

theorem integrable_weighted_tail (G : Ω → ℝ) (hG : Integrable G μ)
    (V : Ω → I) (hV : Measurable V) (t : I) :
    Integrable (fun ω => G ω * tailIndicator (V ω) t) μ := by
  have he : (fun ω => G ω * tailIndicator (V ω) t) = {ω | t < V ω}.indicator G := by
    funext ω
    by_cases h : t < V ω <;> simp [tailIndicator, Set.indicator, h]
  rw [he]
  exact hG.indicator (measurableSet_lt measurable_const hV)

theorem integrable_tail_prod (G : Ω → ℝ) (hG : Integrable G μ)
    (V : Ω → I) (hV : Measurable V) :
    Integrable (fun p : Ω × I => G p.1 * tailIndicator (V p.1) p.2) (μ.prod volume) := by
  have he : (fun p : Ω × I => G p.1 * tailIndicator (V p.1) p.2) =
      {p : Ω × I | p.2 < V p.1}.indicator (fun p => G p.1) := by
    funext p
    by_cases h : p.2 < V p.1 <;> simp [tailIndicator, Set.indicator, h]
  rw [he]
  exact (hG.comp_fst (volume : Measure I)).indicator
    (measurableSet_lt measurable_snd (hV.comp measurable_fst))

theorem weighted_tail_layercake [SFinite μ] (G : Ω → ℝ) (hG : Integrable G μ)
    (V : Ω → I) (hV : Measurable V) :
    (∫ t : I, ∫ ω, G ω * tailIndicator (V ω) t ∂μ) = ∫ ω, G ω * (V ω : ℝ) ∂μ := by
  rw [← integral_integral_swap (integrable_tail_prod G hG V hV)]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [integral_const_mul, integral_tailIndicator]

theorem weighted_tail_shift [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Integrable G μ)
    (V : Ω → I) (hV : MeasurePreserving V μ volume) (t : I) (q : ℝ) :
    (∫ ω, (G ω - q) * tailIndicator (V ω) t ∂μ) =
      (∫ ω, G ω * tailIndicator (V ω) t ∂μ) - q * (1 - (t : ℝ)) := by
  have ht : Integrable (fun ω => tailIndicator (V ω) t) μ := by
    simpa using integrable_weighted_tail (fun _ : Ω => (1 : ℝ)) (integrable_const 1) V hV.measurable t
  have he : (fun ω => (G ω - q) * tailIndicator (V ω) t) =
      fun ω => G ω * tailIndicator (V ω) t - q * tailIndicator (V ω) t := by funext ω; ring
  rw [he, integral_sub (integrable_weighted_tail G hG V hV.measurable t) (ht.const_mul q),
    integral_const_mul, integral_uniform_tail V hV]

/-- Among equal-probability events, the strict upper-tail event uniquely maximizes the G integral. -/
theorem threshold_rearrangement [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Integrable G μ)
    (H V : Ω → I) (hH : MeasurePreserving H μ volume) (hV : MeasurePreserving V μ volume)
    (t : I) (q : ℝ)
    (halign : ∀ᵐ ω ∂μ, (t < H ω ↔ q < G ω) ∧ G ω ≠ q) :
    (∫ ω, G ω * tailIndicator (V ω) t ∂μ) ≤ (∫ ω, G ω * tailIndicator (H ω) t ∂μ) ∧
    ((∫ ω, G ω * tailIndicator (V ω) t ∂μ) = (∫ ω, G ω * tailIndicator (H ω) t ∂μ) ↔
      ∀ᵐ ω ∂μ, tailIndicator (V ω) t = tailIndicator (H ω) t) := by
  let f := fun ω => (G ω - q) * tailIndicator (H ω) t - (G ω - q) * tailIndicator (V ω) t
  have hi : Integrable f μ :=
    (integrable_weighted_tail _ (hG.sub (integrable_const q)) H hH.measurable t).sub
      (integrable_weighted_tail _ (hG.sub (integrable_const q)) V hV.measurable t)
  have hn : ∀ᵐ ω ∂μ, 0 ≤ f ω := by
    filter_upwards [halign] with ω hω
    by_cases hh : t < H ω
    · have hg := hω.1.mp hh
      by_cases hv : t < V ω <;> simp [f, tailIndicator, hh, hv, hg.le]
    · have hg : G ω ≤ q := le_of_not_gt (fun h => hh (hω.1.mpr h))
      by_cases hv : t < V ω <;> simp [f, tailIndicator, hh, hv, hg]
  have he : (∫ ω, f ω ∂μ) = (∫ ω, G ω * tailIndicator (H ω) t ∂μ) -
      (∫ ω, G ω * tailIndicator (V ω) t ∂μ) := by
    change (∫ ω, (G ω - q) * tailIndicator (H ω) t - (G ω - q) * tailIndicator (V ω) t ∂μ) = _
    have hsub := integral_sub
      (integrable_weighted_tail _ (hG.sub (integrable_const q)) H hH.measurable t)
      (integrable_weighted_tail _ (hG.sub (integrable_const q)) V hV.measurable t)
    simp only [Pi.sub_apply] at hsub
    rw [hsub, weighted_tail_shift G hG H hH, weighted_tail_shift G hG V hV]
    ring
  refine ⟨by linarith [integral_nonneg_of_ae hn], ?_⟩
  constructor
  · intro heq
    have hz : (∫ ω, f ω ∂μ) = 0 := by linarith
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    filter_upwards [hzero, halign] with ω hω ha
    by_cases hh : t < H ω <;> by_cases hv : t < V ω
    · simp [tailIndicator, hh, hv]
    · have hg := ha.1.mp hh
      have hf : f ω = 0 := hω
      simp [f, tailIndicator, hh, hv] at hf
      linarith
    · have hg : G ω < q := lt_of_le_of_ne (le_of_not_gt (fun h => hh (ha.1.mpr h))) ha.2
      have hf : f ω = 0 := hω
      simp [f, tailIndicator, hh, hv] at hf
      linarith
    · simp [tailIndicator, hh, hv]
  · intro ha
    apply integral_congr_ae
    filter_upwards [ha] with ω hω
    rw [hω]

def cdfRank (μ : Measure Ω) (G : Ω → ℝ) (ω : Ω) : I := cdfUnit (μ.map G) (G ω)

theorem cdfRank_uniform [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Measurable G)
    (hc : Continuous (ProbabilityTheory.cdf (μ.map G))) :
    MeasurePreserving (cdfRank μ G) μ volume := by
  refine ⟨(measurable_cdfUnit _).comp hG, ?_⟩
  change μ.map (cdfUnit (μ.map G) ∘ G) = volume
  rw [← Measure.map_map (measurable_cdfUnit _) hG, map_cdfUnit _ hc]

theorem cdfRank_threshold [IsProbabilityMeasure μ] (G : Ω → ℝ) (hG : Measurable G)
    (hc : Continuous (ProbabilityTheory.cdf (μ.map G))) (t : I) (ht : (t : ℝ) ∈ Ioo (0 : ℝ) 1) :
    ∃ q : ℝ, ∀ᵐ ω ∂μ, (t < cdfRank μ G ω ↔ q < G ω) ∧ G ω ≠ q := by
  obtain ⟨q, hq⟩ := exists_cdf_eq_of_continuous (μ.map G) hc ht.1 ht.2
  refine ⟨q, ?_⟩
  filter_upwards [uniform_ae_ne (cdfRank μ G) (cdfRank_uniform G hG hc) t] with ω hω
  have hn : ProbabilityTheory.cdf (μ.map G) (G ω) ≠ (t : ℝ) := by
    intro he
    exact hω (Subtype.ext he)
  constructor
  · constructor
    · intro h
      change (t : ℝ) < ProbabilityTheory.cdf (μ.map G) (G ω) at h
      by_contra hle
      have hm := ProbabilityTheory.monotone_cdf (μ.map G) (le_of_not_gt hle)
      rw [hq] at hm
      linarith
    · intro h
      have hm := ProbabilityTheory.monotone_cdf (μ.map G) h.le
      rw [hq] at hm
      change (t : ℝ) < ProbabilityTheory.cdf (μ.map G) (G ω)
      exact lt_of_le_of_ne hm (Ne.symm hn)
  · intro he
    exact hn (he ▸ hq)

/-- The manuscript's general rearrangement inequality and its almost-sure equality case.
G is merely integrable; neither boundedness nor a strictly increasing CDF is assumed. -/
theorem rearrangement [IsProbabilityMeasure μ] (G : Ω → ℝ) (hGm : Measurable G)
    (hG : Integrable G μ) (hc : Continuous (ProbabilityTheory.cdf (μ.map G)))
    (V : Ω → I) (hV : MeasurePreserving V μ volume) :
    (∫ ω, G ω * (V ω : ℝ) ∂μ) ≤ (∫ ω, G ω * ProbabilityTheory.cdf (μ.map G) (G ω) ∂μ) ∧
    ((∫ ω, G ω * (V ω : ℝ) ∂μ) = (∫ ω, G ω * ProbabilityTheory.cdf (μ.map G) (G ω) ∂μ) ↔
      ∀ᵐ ω ∂μ, (V ω : ℝ) = ProbabilityTheory.cdf (μ.map G) (G ω)) := by
  let H := cdfRank μ G
  have hH := cdfRank_uniform G hGm hc
  let gap := fun t : I => (∫ ω, G ω * tailIndicator (H ω) t ∂μ) - (∫ ω, G ω * tailIndicator (V ω) t ∂μ)
  have hiH := (integrable_tail_prod G hG H hH.measurable).integral_prod_right
  have hiV := (integrable_tail_prod G hG V hV.measurable).integral_prod_right
  have hi : Integrable gap := hiH.sub hiV
  have h0 : ∀ᵐ t : I, t ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ t : I, t ≠ 1 := by simp [ae_iff]
  have ht : ∀ᵐ t : I, 0 ≤ gap t ∧ (gap t = 0 ↔ ∀ᵐ ω ∂μ, tailIndicator (V ω) t = tailIndicator (H ω) t) := by
    filter_upwards [h0, h1] with t ht0 ht1
    have htr : (t : ℝ) ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne t.property.1 (Ne.symm (fun h => ht0 (Subtype.ext h))),
        lt_of_le_of_ne t.property.2 (fun h => ht1 (Subtype.ext h))⟩
    obtain ⟨q, hq⟩ := cdfRank_threshold G hGm hc t htr
    have h := threshold_rearrangement G hG H V hH hV t q hq
    refine ⟨sub_nonneg.mpr h.1, ?_⟩
    constructor
    · intro he
      exact h.2.mp (by change _ - _ = 0 at he; linarith)
    · intro he
      have hh := h.2.mpr he
      change _ - _ = 0
      linarith
  have hn : ∀ᵐ t : I, 0 ≤ gap t := ht.mono (fun _ h => h.1)
  have he : (∫ t : I, gap t) =
      (∫ ω, G ω * ProbabilityTheory.cdf (μ.map G) (G ω) ∂μ) - (∫ ω, G ω * (V ω : ℝ) ∂μ) := by
    change (∫ t : I, (∫ ω, G ω * tailIndicator (H ω) t ∂μ) - (∫ ω, G ω * tailIndicator (V ω) t ∂μ)) = _
    rw [integral_sub hiH hiV, weighted_tail_layercake G hG H hH.measurable,
      weighted_tail_layercake G hG V hV.measurable]
    rfl
  refine ⟨by linarith [integral_nonneg_of_ae hn], ?_⟩
  constructor
  · intro heq
    have hz : (∫ t : I, gap t) = 0 := by linarith
    have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    have hteq : ∀ᵐ t : I, ∀ᵐ ω ∂μ, tailIndicator (V ω) t = tailIndicator (H ω) t := by
      filter_upwards [hzero, ht] with t ht0 htp
      exact htp.2.mp ht0
    have hm : MeasurableSet {p : Ω × I | tailIndicator (V p.1) p.2 = tailIndicator (H p.1) p.2} := by
      apply measurableSet_eq_fun
      · exact measurable_const.ite (measurableSet_lt measurable_snd (hV.measurable.comp measurable_fst)) measurable_const
      · exact measurable_const.ite (measurableSet_lt measurable_snd (hH.measurable.comp measurable_fst)) measurable_const
    have hωeq := (Measure.ae_ae_comm hm).mpr hteq
    filter_upwards [hωeq] with ω hω
    have h := integral_congr_ae hω
    rw [integral_tailIndicator, integral_tailIndicator] at h
    exact h
  · intro ha
    apply integral_congr_ae
    filter_upwards [ha] with ω hω
    rw [hω]

#assert_standard_axioms Papers.Rockel2026ExactBlest.cdfRank_uniform
#assert_standard_axioms Papers.Rockel2026ExactBlest.cdfRank_threshold
#assert_standard_axioms Papers.Rockel2026ExactBlest.rearrangement

#assert_standard_axioms Papers.Rockel2026ExactBlest.weighted_tail_shift
#assert_standard_axioms Papers.Rockel2026ExactBlest.threshold_rearrangement

#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_tailIndicator
#assert_standard_axioms Papers.Rockel2026ExactBlest.integral_uniform_tail
#assert_standard_axioms Papers.Rockel2026ExactBlest.uniform_ae_ne
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_weighted_tail
#assert_standard_axioms Papers.Rockel2026ExactBlest.integrable_tail_prod
#assert_standard_axioms Papers.Rockel2026ExactBlest.weighted_tail_layercake

end
end Papers.Rockel2026ExactBlest
