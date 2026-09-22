import Copula.Distribution.ProbabilityIntegralTransform
import Copula.Sklar.Continuous
import Copula.Rank.Integration
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

open MeasureTheory ProbabilityTheory Set Filter
open Copula
open scoped unitInterval

namespace Verification

/-- A measurable band of fixed positive width, with a uniform conditional law in each row. -/
structure IncreasingBand where
  width : ℝ
  width_pos : 0 < width
  width_le_one : width ≤ 1
  lower : I → ℝ
  lower_measurable : Measurable lower
  lower_nonneg : ∀ u, 0 ≤ lower u
  lower_le : ∀ u, lower u ≤ 1-width

namespace IncreasingBand

variable (B : IncreasingBand)

noncomputable def density (p : I × I) : ℝ :=
  if B.lower p.1 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ B.lower p.1+B.width then 1/B.width else 0

theorem density_measurable : Measurable B.density := by
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le (B.lower_measurable.comp measurable_fst) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) ((B.lower_measurable.comp measurable_fst).add_const _))

theorem density_mem (p : I × I) : B.density p ∈ Icc 0 (1/B.width) := by
  have hb : 0 < B.width := B.width_pos
  unfold density
  split_ifs
  · exact ⟨by positivity,le_rfl⟩
  · exact ⟨le_rfl,by positivity⟩

theorem density_integrable : Integrable B.density := by
  refine (integrable_const (1/B.width)).mono' B.density_measurable.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (B.density_mem p).1]
  exact (B.density_mem p).2

theorem density_row_integrable (u : I) : Integrable (fun v : I => B.density (u,v)) := by
  refine (integrable_const (1/B.width)).mono' (B.density_measurable.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs,abs_of_nonneg (B.density_mem (u,v)).1]
  exact (B.density_mem (u,v)).2

theorem density_row_integral (u : I) : (∫ v : I, B.density (u,v))=1 := by
  let a : I := ⟨B.lower u,B.lower_nonneg u,by linarith [B.lower_le u,B.width_pos]⟩
  let b : I := ⟨B.lower u+B.width,by linarith [B.lower_nonneg u,B.width_pos],by linarith [B.lower_le u]⟩
  have he : (fun v : I => B.density (u,v)) = (Icc a b).indicator (fun _ => 1/B.width) := by
    funext v
    change (if B.lower u ≤ (v:ℝ) ∧ (v:ℝ) ≤ B.lower u+B.width then 1/B.width else 0) = _
    simp only [indicator,mem_Icc]
    change (if a ≤ v ∧ v ≤ b then _ else _) = (if a ≤ v ∧ v ≤ b then _ else _)
    split_ifs <;> rfl
  rw [he,integral_indicator measurableSet_Icc,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,unitInterval.volume_Icc,smul_eq_mul]
  have hab : (b:ℝ)-(a:ℝ)=B.width := by dsimp [a,b]; ring
  rw [hab,ENNReal.toReal_ofReal B.width_pos.le]
  exact mul_one_div_cancel B.width_pos.ne'

theorem density_integral : (∫ p : I × I, B.density p)=1 := by
  change (∫ p : I × I, B.density p ∂(volume.prod volume))=1
  rw [integral_prod _ B.density_integrable]
  simp only [B.density_row_integral,integral_const,probReal_univ,smul_eq_mul,mul_one]

noncomputable def measure : Measure (I × I) := volume.withDensity (fun p => ENNReal.ofReal (B.density p))

instance : IsProbabilityMeasure B.measure := by
  refine ⟨?_⟩
  rw [measure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal B.density_integrable (Eventually.of_forall fun p => (B.density_mem p).1),B.density_integral]
  norm_num

theorem integral_measure (f : I × I → ℝ) : (∫ p, f p ∂B.measure)=∫ p, B.density p*f p := by
  rw [measure,integral_withDensity_eq_integral_toReal_smul B.density_measurable.ennreal_ofReal (by simp)]
  simp only [ENNReal.toReal_ofReal (B.density_mem _).1,smul_eq_mul]

theorem map_fst : B.measure.map Prod.fst=volume := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map measurable_fst.aemeasurable f.continuous.measurable.aestronglyMeasurable,B.integral_measure]
  have hi : Integrable (fun p : I × I => B.density p*f p.1) :=
    B.density_integrable.mul_bdd (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => f.norm_coe_le_norm p.1)
  change (∫ p : I × I, B.density p*f p.1 ∂(volume.prod volume))=_
  rw [integral_prod _ hi]
  simp only [integral_mul_const,B.density_row_integral,one_mul]

noncomputable def secondLaw : Measure ℝ := B.measure.map (fun p => (p.2 : ℝ))

instance : IsProbabilityMeasure B.secondLaw := by
  unfold secondLaw
  constructor
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,Set.preimage_univ,measure_univ]

instance : NullSingletonClass B.secondLaw := by
  constructor
  intro t
  rw [secondLaw,Measure.map_apply (by fun_prop) (measurableSet_singleton t)]
  apply withDensity_absolutelyContinuous (volume : Measure (I × I)) (fun p => ENNReal.ofReal (B.density p))
  let S : Set I := {v | (v : ℝ)=t}
  have hs : S.Subsingleton := by
    intro x hx y hy
    apply Subtype.ext
    exact hx.trans hy.symm
  have hm : MeasurableSet S := measurableSet_eq_fun (by fun_prop) measurable_const
  change (volume : Measure (I × I)) (Prod.snd ⁻¹' S)=0
  rw [← Measure.map_apply measurable_snd hm]
  change ((volume : Measure I).prod volume).map Prod.snd S=0
  rw [Measure.map_snd_prod,measure_univ,one_smul]
  exact hs.countable.measure_zero volume

noncomputable def sample (p : I × I) : Fin 2 → I := ![p.1,cdfUnit B.secondLaw p.2]

theorem sample_measurable : Measurable B.sample := by
  unfold sample
  fun_prop

theorem sample_marginal (d : Fin 2) : B.measure.map (fun p => B.sample p d)=volume := by
  fin_cases d
  · exact B.map_fst
  · change B.measure.map (cdfUnit B.secondLaw ∘ (fun p : I × I => (p.2 : ℝ)))=volume
    rw [← Measure.map_map (measurable_cdfUnit _) (by fun_prop)]
    exact map_cdfUnit B.secondLaw (continuous_cdf_of_atomless B.secondLaw)

/-- Standardize the second marginal of the uniform density inside the band. -/
noncomputable def copula : Copula 2 :=
  Copula.ofMap ⟨B.measure,inferInstance⟩ B.sample B.sample_measurable B.sample_marginal

theorem copula_law : B.copula.toMeasure=B.measure.map B.sample := rfl


end IncreasingBand
end Verification
