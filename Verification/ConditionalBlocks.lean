import Verification.NormalizedConditionalCDF
import Verification.UnitSplit
import Verification.ConditionalCopulaAE

/-! # Affine localization of two conditional models into diagonal blocks -/

open MeasureTheory ProbabilityTheory Set Copula.OrdinalSum
open scoped unitInterval

namespace Verification

noncomputable def blockKernel (C D : Copula 2) (a v u : I) : ℝ :=
  unitJoin a (fun t => normalizedCDF C t (lowerCoord a v))
    (fun t => normalizedCDF D t (upperCoord a v)) u

theorem blockKernel_measurable (C D : Copula 2) (a : I) :
    Measurable (fun p : I × I => blockKernel C D a p.1 p.2) := by
  have hL := (continuous_lowerCoord a).measurable
  have hU := (continuous_upperCoord a).measurable
  exact ((normalizedCDF_measurable C).comp
    ((hL.comp measurable_fst).prodMk (hL.comp measurable_snd))).ite
    (measurableSet_le measurable_snd measurable_const)
    ((normalizedCDF_measurable D).comp
    ((hU.comp measurable_fst).prodMk (hU.comp measurable_snd)))

theorem blockKernel_mem (C D : Copula 2) (a v u : I) : blockKernel C D a v u ∈ Icc (0 : ℝ) 1 := by
  unfold blockKernel unitJoin
  split_ifs <;> exact normalizedCDF_mem _ _ _

theorem blockKernel_integrable (C D : Copula 2) (a v : I) : Integrable (blockKernel C D a v) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((blockKernel_measurable C D a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (blockKernel_mem C D a v u).1]
    exact (blockKernel_mem C D a v u).2

theorem blockKernel_mean (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) (v : I) :
    (∫ u : I, blockKernel C D a v u) = v := by
  simp only [blockKernel]
  rw [integral_unitJoin a ha0 ha1 (fun t => normalizedCDF C t (lowerCoord a v)) (fun t => normalizedCDF D t (upperCoord a v))
    ((normalizedCDF_measurable C).comp (measurable_const.prodMk measurable_id))
    ((normalizedCDF_measurable D).comp (measurable_const.prodMk measurable_id))
    (normalizedCDF_integrable C _) (normalizedCDF_integrable D _),
    normalizedCDF_mean,normalizedCDF_mean,weighted_coords]

theorem blockKernel_mono (C D : Copula 2) (a u : I) : Monotone (fun v => blockKernel C D a v u) := by
  intro v w hvw
  unfold blockKernel unitJoin
  split_ifs
  · exact normalizedCDF_mono C _ (lowerCoord_mono a hvw)
  · exact normalizedCDF_mono D _ (upperCoord_mono a hvw)

theorem blockKernel_zero (C D : Copula 2) (a : I) : blockKernel C D a 0 =ᵐ[volume] fun _ => 0 := by
  exact Filter.Eventually.of_forall fun u => by simp [blockKernel,unitJoin,normalizedCDF_zero]

theorem blockKernel_one (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    blockKernel C D a 1 =ᵐ[volume] fun _ => 1 := by
  exact Filter.Eventually.of_forall fun u => by
    simp [blockKernel,unitJoin,lowerCoord_one a ha0,upperCoord_one a ha1,normalizedCDF_one]

noncomputable def conditionalBlocks (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) : Copula 2 :=
  copulaOfConditionalAE (blockKernel C D a) (blockKernel_integrable C D a)
    (blockKernel_mono C D a) (blockKernel_zero C D a) (blockKernel_one C D a ha0 ha1)
    (blockKernel_mean C D a ha0 ha1)

theorem conditionalBlocks_conditionalCDF (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) (v : I) :
    (fun u => (conditionalBlocks C D a ha0 ha1).conditionalCDF u v) =ᵐ[volume] blockKernel C D a v :=
  copulaOfConditionalAE_kernel _ _ _ _ _ _ (fun v u => (blockKernel_mem C D a v u).1) v

theorem conditionalMean_conditionalBlocks (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    conditionalMean (conditionalBlocks C D a ha0 ha1) =ᵐ[volume]
      unitJoin a (fun u => (a : ℝ)*conditionalMean C u)
        (fun u => (a : ℝ)+(1-(a : ℝ))*conditionalMean D u) := by
  have hae : ∀ᵐ u : I, ∀ᵐ v : I,
      (conditionalBlocks C D a ha0 ha1).conditionalCDF u v = blockKernel C D a v u :=
    (Measure.ae_ae_comm (μ := (volume : Measure I)) (ν := (volume : Measure I))
      (p := fun v u : I => (conditionalBlocks C D a ha0 ha1).conditionalCDF u v = blockKernel C D a v u)
      (measurableSet_eq_fun (conditionalBlocks C D a ha0 ha1).measurable_conditionalCDF
        (blockKernel_measurable C D a))).mp
      (Filter.Eventually.of_forall (conditionalBlocks_conditionalCDF C D a ha0 ha1))
  filter_upwards [hae] with u hu
  rw [conditionalMean_eq,integral_congr_ae hu]
  unfold blockKernel unitJoin
  by_cases h : u ≤ a
  · simp only [ite_eq_left h]
    rw [integral_lowerCoord a ha0 (normalizedCDF C (lowerCoord a u))
      ((normalizedCDF_measurable C).comp (measurable_id.prodMk measurable_const))
      (normalizedCDF_response_integrable C _),normalizedCDF_one,normalizedCDF_response_integral]
    ring
  · simp only [ite_eq_right h]
    rw [integral_upperCoord a ha1 (normalizedCDF D (upperCoord a u))
      ((normalizedCDF_measurable D).comp (measurable_id.prodMk measurable_const))
      (normalizedCDF_response_integrable D _),normalizedCDF_zero,normalizedCDF_response_integral]
    ring

end Verification
