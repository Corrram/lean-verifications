import Verification.CopulaOptimization
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Topology.MetricSpace.Polish

open MeasureTheory TopologicalSpace Set
open scoped unitInterval NNReal ENNReal

namespace Verification

private theorem borel_le_of_initial {α β ι : Type*} [t : TopologicalSpace α]
    [SecondCountableTopology α] [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] (f : ι → α → β)
    (ht : t = ⨅ i, induced (f i) inferInstance) (hf : ∀ i, Measurable (f i)) :
    borel α ≤ ‹MeasurableSpace α› := by
  rw [borel_eq_generateFrom_of_subbasis (ht.trans (generateFrom_iUnion_isOpen _).symm)]
  apply MeasurableSpace.generateFrom_le
  rintro s ⟨_, ⟨i, rfl⟩, hs⟩
  obtain ⟨u, hu, rfl⟩ := isOpen_induced_iff.mp hs
  exact (hf i) hu.measurableSet

instance probabilityUnitOpensMeasurable : OpensMeasurableSpace (ProbabilityMeasure I) := by
  constructor
  apply borel_le_of_initial
    (fun (f : BoundedContinuousFunction I ℝ≥0) (μ : ProbabilityMeasure I) => μ.toFiniteMeasure.testAgainstNN f)
  · change induced ProbabilityMeasure.toFiniteMeasure
      (induced FiniteMeasure.toWeakDualBCNN
        (induced (fun x y => x y) Pi.topologicalSpace)) = _
    simp only [induced_compose, Pi.topologicalSpace, induced_iInf]
    rfl
  · intro f
    exact ((Measure.measurable_lintegral f.continuous.measurable.coe_nnreal_ennreal).comp
      measurable_subtype_coe).ennreal_toNNReal

/-- Evaluation on a Borel set is measurable for the weak Borel structure. -/
private theorem weakBorel_measurable_eval (s : Set I) (hs : MeasurableSet s) :
    @Measurable (ProbabilityMeasure I) ℝ≥0∞ (borel _) inferInstance
      (fun μ => μ.toMeasure s) := by
  let : MeasurableSpace (ProbabilityMeasure I) := borel _
  let : BorelSpace (ProbabilityMeasure I) := ⟨rfl⟩
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen s hs =>
    apply LowerSemicontinuous.measurable
    rw [lowerSemicontinuous_iff_le_liminf]
    intro μ
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto Filter.tendsto_id hs
  | compl s hs ih =>
    have he : (fun μ : ProbabilityMeasure I => μ.toMeasure sᶜ) =
        fun μ => 1 - μ.toMeasure s := by
      funext μ
      simp [measure_compl hs (measure_ne_top _ _)]
    rw [he]
    exact measurable_const.sub ih
  | iUnion f hd hf ih =>
    have he : (fun μ : ProbabilityMeasure I => μ.toMeasure (⋃ i, f i)) =
        fun μ => ∑' i, μ.toMeasure (f i) := by
      funext μ
      exact measure_iUnion hd hf
    rw [he]
    exact Measurable.tsum ih

/-- On laws on the unit interval, the Giry and weak Borel structures agree. -/
instance probabilityUnitBorel : BorelSpace (ProbabilityMeasure I) := by
  constructor
  apply le_antisymm
  · change MeasurableSpace.comap Subtype.val
      (⨆ (s : Set I) (_ : MeasurableSet s), (borel ℝ≥0∞).comap (fun μ : Measure I => μ s)) ≤ _
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup_le fun s => iSup_le fun hs => ?_
    exact (weakBorel_measurable_eval s hs).comap_le
  · exact OpensMeasurableSpace.borel_le

instance probabilityUnitPolish : PolishSpace (ProbabilityMeasure I) := by
  let := TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure I)
  infer_instance

end Verification
