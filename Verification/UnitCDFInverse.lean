import Copula.Distribution.Quantile
import Copula.Distribution.ProbabilityIntegralTransform
import Copula.Rank.Integration

open MeasureTheory ProbabilityTheory Set Filter
open scoped unitInterval Topology

namespace Verification

variable (μ : Measure I) [IsProbabilityMeasure μ] [NullSingletonClass μ]

noncomputable def unitCDF (t : I) : I := ⟨μ.real (Iic t),measureReal_nonneg,measureReal_le_one⟩

omit [NullSingletonClass μ] in
theorem unitCDF_eq (t : I) : unitCDF μ t=cdfUnit (μ.map ((↑) : I → ℝ)) t := by
  apply Subtype.ext
  rw [coe_cdfUnit,ProbabilityTheory.unitInterval.cdf_eq_real]
  apply congrArg μ.real
  ext x
  exact ⟨fun hx => ⟨x.property.1,hx⟩,fun hx => hx.2⟩

omit [IsProbabilityMeasure μ] in
theorem unitCDF_real_atomless : NullSingletonClass (μ.map ((↑) : I → ℝ)) := by
  constructor
  intro t
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton t)]
  have hs : (((↑) : I → ℝ) ⁻¹' {t}).Subsingleton := by
    intro x hx y hy
    apply Subtype.ext
    exact hx.trans hy.symm
  exact hs.countable.measure_zero μ

theorem unitCDF_continuous : Continuous (unitCDF μ) := by
  have := unitCDF_real_atomless μ
  have hc := continuous_cdf_of_atomless (μ.map ((↑) : I → ℝ))
  have he : unitCDF μ=(fun t : I => cdfUnit (μ.map ((↑) : I → ℝ)) t) := funext (unitCDF_eq μ)
  rw [he]
  exact (hc.comp continuous_subtype_val).subtype_mk _

theorem unitCDF_map : μ.map (unitCDF μ)=volume := by
  have := unitCDF_real_atomless μ
  have he : unitCDF μ=cdfUnit (μ.map ((↑) : I → ℝ)) ∘ ((↑) : I → ℝ) := funext (unitCDF_eq μ)
  rw [he,← Measure.map_map (measurable_cdfUnit _) measurable_subtype_coe]
  exact map_cdfUnit _ (continuous_cdf_of_atomless _)

theorem unitCDF_zero : unitCDF μ 0=0 := by
  apply Subtype.ext
  change μ.real (Iic (0 : I))=0
  have he : Iic (0 : I)={0} := by
    ext t
    change (t ≤ 0 ↔ t=0)
    exact ⟨fun h => le_antisymm h t.property.1,fun h => h.le⟩
  simp only [he,Measure.real,measure_singleton,ENNReal.toReal_zero]

omit [NullSingletonClass μ] in
theorem unitCDF_one : unitCDF μ 1=1 := by
  apply Subtype.ext
  change μ.real (Iic (1 : I))=1
  have he : Iic (1 : I)=univ := by
    ext t
    simp only [mem_Iic,mem_univ,iff_true]
    exact t.property.2
  rw [he,probReal_univ]

theorem unitCDF_surjective : Function.Surjective (unitCDF μ) := by
  intro v
  have h := intermediate_value_Icc (show (0 : I) ≤ 1 from zero_le_one)
    (unitCDF_continuous μ).continuousOn
    (show v ∈ Icc (unitCDF μ 0) (unitCDF μ 1) by rw [unitCDF_zero,unitCDF_one]; exact v.property)
  obtain ⟨t,_,ht⟩ := h
  exact ⟨t,ht⟩

theorem unitCDF_quantile (v : I) : unitCDF μ (unitQuantile μ v)=v := by
  obtain ⟨t,ht⟩ := unitCDF_surjective μ v
  apply le_antisymm
  · have hq : unitQuantile μ v ≤ t := (unitQuantile_le_iff μ v t).mpr (show (v : ℝ) ≤ μ.real (Iic t) by rw [← ht]; rfl)
    have hm : Monotone (unitCDF μ) := fun _ _ h => measureReal_mono (Iic_subset_Iic.mpr h)
    exact (hm hq).trans ht.le
  · exact (unitQuantile_le_iff μ v (unitQuantile μ v)).mp le_rfl

/-- Flat intervals are harmless: the quantile is a left inverse almost surely. -/
theorem quantile_unitCDF_ae : (fun t => unitQuantile μ (unitCDF μ t)) =ᵐ[μ] id := by
  have hm : Measurable (fun t => unitQuantile μ (unitCDF μ t)) :=
    (measurable_unitQuantile μ).comp (unitCDF_continuous μ).measurable
  have hl : ∀ t : I, unitQuantile μ (unitCDF μ t) ≤ t :=
    fun t => (unitQuantile_le_iff μ (unitCDF μ t) t).mpr le_rfl
  have hmap : μ.map (fun t => unitQuantile μ (unitCDF μ t))=μ := by
    change μ.map (unitQuantile μ ∘ unitCDF μ)=μ
    rw [← Measure.map_map (measurable_unitQuantile μ) (unitCDF_continuous μ).measurable,unitCDF_map,map_unitQuantile]
  have hi : Integrable (fun t : I => (t : ℝ)) μ := Copula.integrable_continuous_unit μ (by fun_prop)
  have hj : Integrable (fun t : I => (unitQuantile μ (unitCDF μ t) : ℝ)) μ :=
    (integrable_const (1 : ℝ)).mono' (measurable_subtype_coe.comp hm).aestronglyMeasurable
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (unitQuantile μ (unitCDF μ t)).property.1]; exact (unitQuantile μ (unitCDF μ t)).property.2)
  have he : (∫ t : I, (unitQuantile μ (unitCDF μ t) : ℝ) ∂μ)=∫ t : I, (t : ℝ) ∂μ := by
    rw [← integral_map hm.aemeasurable (by fun_prop),hmap]
  have hae := (integral_eq_iff_of_ae_le hj hi (Eventually.of_forall hl)).mp he
  filter_upwards [hae] with t ht
  exact Subtype.ext ht

end Verification
