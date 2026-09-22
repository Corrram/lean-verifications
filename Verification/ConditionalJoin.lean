import Verification.UnitSplit
import Verification.ConditionalCopulaAE

/-! # Copulas obtained by tagging two conditional models on predictor blocks -/

open MeasureTheory ProbabilityTheory Set Copula.OrdinalSum
open scoped unitInterval

namespace Verification

noncomputable def joinKernel (C D : Copula 2) (a v u : I) : ℝ :=
  unitJoin a (fun t => C.conditionalCDF t v) (fun t => D.conditionalCDF t v) u

theorem joinKernel_measurable (C D : Copula 2) (a : I) :
    Measurable (fun p : I × I => joinKernel C D a p.1 p.2) := by
  exact (C.measurable_conditionalCDF.comp
    (measurable_fst.prodMk ((continuous_lowerCoord a).measurable.comp measurable_snd))).ite
    (measurableSet_le measurable_snd measurable_const)
    (D.measurable_conditionalCDF.comp
    (measurable_fst.prodMk ((continuous_upperCoord a).measurable.comp measurable_snd)))

theorem joinKernel_mem (C D : Copula 2) (a v u : I) :
    joinKernel C D a v u ∈ Icc (0 : ℝ) 1 := by
  unfold joinKernel unitJoin
  split_ifs
  · exact ⟨C.conditionalCDF_nonneg _ _,C.conditionalCDF_le_one _ _⟩
  · exact ⟨D.conditionalCDF_nonneg _ _,D.conditionalCDF_le_one _ _⟩

theorem joinKernel_integrable (C D : Copula 2) (a v : I) : Integrable (joinKernel C D a v) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((joinKernel_measurable C D a).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (joinKernel_mem C D a v u).1]
    exact (joinKernel_mem C D a v u).2

theorem joinKernel_mean (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) (v : I) :
    (∫ u : I, joinKernel C D a v u) = v := by
  simp only [joinKernel]
  rw [integral_unitJoin a ha0 ha1 _ _
    (C.measurable_conditionalCDF_left v) (D.measurable_conditionalCDF_left v)
    (C.integrable_conditionalCDF v) (D.integrable_conditionalCDF v),
    C.integral_conditionalCDF,D.integral_conditionalCDF]
  ring

theorem joinKernel_mono (C D : Copula 2) (a u : I) : Monotone (fun v => joinKernel C D a v u) := by
  intro v w hvw
  unfold joinKernel unitJoin
  split_ifs
  all_goals exact measureReal_mono (Iic_subset_Iic.mpr hvw)

theorem joinKernel_zero (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    joinKernel C D a 0 =ᵐ[volume] fun _ => 0 := by
  apply (integral_eq_zero_iff_of_nonneg (fun u => (joinKernel_mem C D a 0 u).1)
    (joinKernel_integrable C D a 0)).mp
  exact joinKernel_mean C D a ha0 ha1 0

theorem joinKernel_one (C D : Copula 2) (a : I) :
    joinKernel C D a 1 =ᵐ[volume] fun _ => 1 := by
  have he : Iic (1 : I) = univ := by ext u; simp [unitInterval.le_one']
  exact Filter.Eventually.of_forall fun u => by
    unfold joinKernel unitJoin Copula.conditionalCDF
    split_ifs <;> simp [he]

noncomputable def conditionalJoin (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) : Copula 2 :=
  copulaOfConditionalAE (joinKernel C D a) (joinKernel_integrable C D a)
    (joinKernel_mono C D a) (joinKernel_zero C D a ha0 ha1) (joinKernel_one C D a)
    (joinKernel_mean C D a ha0 ha1)

theorem conditionalJoin_conditionalCDF (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) (v : I) :
    (fun u => (conditionalJoin C D a ha0 ha1).conditionalCDF u v) =ᵐ[volume] joinKernel C D a v :=
  copulaOfConditionalAE_kernel _ _ _ _ _ _ (fun v u => (joinKernel_mem C D a v u).1) v

end Verification
