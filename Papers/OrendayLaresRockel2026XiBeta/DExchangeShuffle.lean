import Papers.OrendayLaresRockel2026XiBeta.IntervalExchange
import Copula.Rank.Region.XiBlest.Support.Shuffle
import Copula.Rank.ChatterjeeExamples

/-! # The shuffle representation of `D_b` and measure preservation of `T_b`

The interval exchange `T_b` is a four-strip increasing shuffle. Using the library's
`PositiveShuffle` (zero-width strips allowed, so no case split at `b = ±1`), we build
the copula `S_b` supported on the graph of `T_b`; from this we deduce that `T_b` is measure
preserving and define `D_b` as the copula of `(U, T_b(U))`, i.e. the pushforward of Lebesgue
measure under `u ↦ (u, T_b u)`.
-/

open MeasureTheory Set ProbabilityTheory
open ProbabilityTheory.Copula.RankRegion.XiBlest.Support
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The four strips of the shuffle representing the graph of `T` with cut point `s`. -/
noncomputable def exchangeStrips {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : Fin 4 → ShuffleStrip :=
  ![⟨0, 0, s, le_rfl, le_rfl, hs.1, by linarith [hs.2], by linarith [hs.2]⟩,
    ⟨s, 1 / 2, 1 / 2 - s, hs.1, by norm_num, by linarith [hs.2], by linarith, by linarith [hs.1]⟩,
    ⟨1 / 2, s, 1 / 2 - s, by norm_num, hs.1, by linarith [hs.2], by linarith [hs.1], by linarith⟩,
    ⟨1 - s, 1 - s, s, by linarith [hs.2], by linarith [hs.2], hs.1, by linarith, by linarith⟩]

noncomputable def exchangeShuffle {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : PositiveShuffle 4 where
  strip := exchangeStrips hs
  total := by
    simp [Fin.sum_univ_four, exchangeStrips]
    ring
  tile_x u := by
    simp [Fin.sum_univ_four, exchangeStrips]
    have hw : 0 ≤ (2⁻¹ : ℝ) - s := by linarith [hs.2]
    rw [stripCut_eq_min_sub hs.1, stripCut_eq_min_sub hw, stripCut_eq_min_sub hw,
      stripCut_eq_min_sub hs.1, show s + (2⁻¹ - s) = 2⁻¹ by ring,
      show 2⁻¹ + (2⁻¹ - s) = 1 - s by ring, show 1 - s + s = 1 by ring, zero_add,
      min_eq_left u.property.2, min_eq_right u.property.1]
    ring
  tile_y u := by
    simp [Fin.sum_univ_four, exchangeStrips]
    have hw : 0 ≤ (2⁻¹ : ℝ) - s := by linarith [hs.2]
    rw [stripCut_eq_min_sub hs.1, stripCut_eq_min_sub hw, stripCut_eq_min_sub hw,
      stripCut_eq_min_sub hs.1, show s + (2⁻¹ - s) = 2⁻¹ by ring,
      show 2⁻¹ + (2⁻¹ - s) = 1 - s by ring, show 1 - s + s = 1 by ring, zero_add,
      min_eq_left u.property.2, min_eq_right u.property.1]
    ring

/-- The copula of the shuffle with the four strips of `T` (cut point `s`). -/
noncomputable def exchangeShuffleCopula {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : Copula 2 :=
  (exchangeShuffle hs).copula

theorem strip_ae_graph_of {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) (S : ShuffleStrip)
    (h : 0 < S.width → ∀ z : I, z ≠ 0 →
      S.y + S.width * (z : ℝ) = xchgReal s (S.x + S.width * (z : ℝ))) :
    ∀ᵐ x ∂S.law, x 1 = xchg s (x 0) := by
  by_cases hw : S.width = 0
  · simp [ShuffleStrip.law, hw]
  have hwpos : 0 < S.width := lt_of_le_of_ne S.width_nonneg (Ne.symm hw)
  unfold ShuffleStrip.law
  refine Measure.ae_smul_measure ?_ _
  refine (ae_map_iff S.continuous_point.measurable.aemeasurable
    (p := fun x : Fin 2 → I => x 1 = xchg s (x 0))
    (measurableSet_eq_fun (measurable_pi_apply 1)
      ((measurable_xchg s).comp (measurable_pi_apply 0)))).2 ?_
  have hz : ∀ᵐ t : I, t ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hz] with z hz
  apply Subtype.ext
  change S.y + S.width * (z : ℝ) = ((xchg s ⟨S.x + S.width * (z : ℝ), _⟩ : I) : ℝ)
  rw [coe_xchg hs]
  exact h hwpos z hz

theorem exchangeShuffle_ae_graph {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
    ∀ᵐ x ∂(exchangeShuffleCopula hs).toMeasure, x 1 = xchg s (x 0) := by
  rw [ae_iff]
  change (∑ i, (exchangeStrips hs i).law) {x | ¬ x 1 = xchg s (x 0)} = 0
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  refine ae_iff.mp ?_
  obtain ⟨hs0, hs1⟩ := hs
  fin_cases i
  · refine strip_ae_graph_of ⟨hs0, hs1⟩ _ ?_
    intro hw z hz
    have hz0 : (0 : ℝ) < z := lt_of_le_of_ne z.property.1 (fun h => hz (Subtype.ext h.symm))
    have hz1 : (z : ℝ) ≤ 1 := z.property.2
    change 0 + s * (z : ℝ) = xchgReal s (0 + s * (z : ℝ))
    have a1 : ¬ (s < 0 + s * (z : ℝ) ∧ 0 + s * (z : ℝ) ≤ 1 / 2) := fun h => by nlinarith [h.1]
    have a2 : ¬ (1 / 2 < 0 + s * (z : ℝ) ∧ 0 + s * (z : ℝ) ≤ 1 - s) := fun h => by nlinarith [h.1]
    rw [xchgReal, ite_eq_right a1, ite_eq_right a2]
  · refine strip_ae_graph_of ⟨hs0, hs1⟩ _ ?_
    intro hw z hz
    have hz0 : (0 : ℝ) < z := lt_of_le_of_ne z.property.1 (fun h => hz (Subtype.ext h.symm))
    have hz1 : (z : ℝ) ≤ 1 := z.property.2
    change 1 / 2 + (1 / 2 - s) * (z : ℝ) = xchgReal s (s + (1 / 2 - s) * (z : ℝ))
    have hw' : (0 : ℝ) < 1 / 2 - s := hw
    have a1 : s < s + (1 / 2 - s) * (z : ℝ) ∧ s + (1 / 2 - s) * (z : ℝ) ≤ 1 / 2 :=
      ⟨by nlinarith, by nlinarith⟩
    rw [xchgReal, ite_eq_left a1]
    ring
  · refine strip_ae_graph_of ⟨hs0, hs1⟩ _ ?_
    intro hw z hz
    have hz0 : (0 : ℝ) < z := lt_of_le_of_ne z.property.1 (fun h => hz (Subtype.ext h.symm))
    have hz1 : (z : ℝ) ≤ 1 := z.property.2
    change s + (1 / 2 - s) * (z : ℝ) = xchgReal s (1 / 2 + (1 / 2 - s) * (z : ℝ))
    have hw' : (0 : ℝ) < 1 / 2 - s := hw
    have a1 : ¬ (s < 1 / 2 + (1 / 2 - s) * (z : ℝ) ∧ 1 / 2 + (1 / 2 - s) * (z : ℝ) ≤ 1 / 2) :=
      fun h => by nlinarith [h.2]
    have a2 : 1 / 2 < 1 / 2 + (1 / 2 - s) * (z : ℝ) ∧
        1 / 2 + (1 / 2 - s) * (z : ℝ) ≤ 1 - s := ⟨by nlinarith, by nlinarith⟩
    rw [xchgReal, ite_eq_right a1, ite_eq_left a2]
    ring
  · refine strip_ae_graph_of ⟨hs0, hs1⟩ _ ?_
    intro hw z hz
    have hz0 : (0 : ℝ) < z := lt_of_le_of_ne z.property.1 (fun h => hz (Subtype.ext h.symm))
    have hz1 : (z : ℝ) ≤ 1 := z.property.2
    change 1 - s + s * (z : ℝ) = xchgReal s (1 - s + s * (z : ℝ))
    have hw' : (0 : ℝ) < s := hw
    have a1 : ¬ (s < 1 - s + s * (z : ℝ) ∧ 1 - s + s * (z : ℝ) ≤ 1 / 2) :=
      fun h => by nlinarith [h.2]
    have a2 : ¬ (1 / 2 < 1 - s + s * (z : ℝ) ∧ 1 - s + s * (z : ℝ) ≤ 1 - s) :=
      fun h => by nlinarith [h.2]
    rw [xchgReal, ite_eq_right a1, ite_eq_right a2]

theorem measurable_graph {f : I → I} (hf : Measurable f) :
    Measurable (fun u : I => ![u, f u]) := by
  refine Measurable.of_eval (fun i => ?_)
  fin_cases i
  · exact measurable_id
  · exact hf

/-- A copula supported a.e. on the graph of a measurable `f` is the law of `(U, f U)`. -/
theorem toMeasure_eq_map_graph (C : Copula 2) {f : I → I} (hf : Measurable f)
    (h : ∀ᵐ x ∂C.toMeasure, x 1 = f (x 0)) :
    C.toMeasure = (volume : Measure I).map (fun u => ![u, f u]) := by
  have hg := measurable_graph hf
  have h1 : (fun x : Fin 2 → I => x) =ᵐ[C.toMeasure] fun x => ![x 0, f (x 0)] := by
    filter_upwards [h] with x hx
    funext i
    fin_cases i
    · rfl
    · exact hx
  have hg' : Measurable (fun x : Fin 2 → I => ![x 0, f (x 0)]) :=
    hg.comp (measurable_pi_apply 0)
  calc C.toMeasure = C.toMeasure.map id := (Measure.map_id).symm
    _ = C.toMeasure.map (fun x => ![x 0, f (x 0)]) := Measure.map_congr h1
    _ = (C.toMeasure.map (fun x => x 0)).map (fun u => ![u, f u]) :=
        (Measure.map_map hg (measurable_pi_apply 0)).symm
    _ = (volume : Measure I).map (fun u => ![u, f u]) := by rw [C.map_eval]

theorem xchg_measurePreserving {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) :
    MeasurePreserving (xchg s) (volume : Measure I) volume := by
  refine ⟨measurable_xchg s, ?_⟩
  have hm := toMeasure_eq_map_graph (exchangeShuffleCopula hs) (measurable_xchg s)
    (exchangeShuffle_ae_graph hs)
  have h1 := (exchangeShuffleCopula hs).map_eval 1
  rw [hm, Measure.map_map (measurable_pi_apply 1) (measurable_graph (measurable_xchg s))] at h1
  exact h1

theorem intervalExchange_measurePreserving {b : ℝ} (hb : b ∈ Icc (-1 : ℝ) 1) :
    MeasurePreserving (intervalExchange b) (volume : Measure I) volume :=
  xchg_measurePreserving (exchangeCut_mem hb)

/-- The copula `D_b` of `(U, T_b(U))` with `U ~ U(0,1)`. -/
noncomputable def dExchange (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) : Copula 2 :=
  Copula.ofMap ⟨volume, inferInstance⟩ (fun u : I => ![u, intervalExchange b u])
    (measurable_graph (measurable_xchg _))
    (by
      intro i
      fin_cases i
      · exact Measure.map_id
      · exact (intervalExchange_measurePreserving hb).map_eq)

theorem toMeasure_dExchange (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    (dExchange b hb).toMeasure =
      (volume : Measure I).map (fun u : I => ![u, intervalExchange b u]) := rfl

theorem dExchange_eq_shuffle (b : ℝ) (hb : b ∈ Icc (-1 : ℝ) 1) :
    dExchange b hb = exchangeShuffleCopula (exchangeCut_mem hb) := by
  apply Copula.ext
  rw [toMeasure_dExchange]
  exact (toMeasure_eq_map_graph _ (measurable_xchg _) (exchangeShuffle_ae_graph _)).symm

end Papers.OrendayLaresRockel2026XiBeta
