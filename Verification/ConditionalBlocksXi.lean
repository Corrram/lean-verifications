import Verification.ConditionalBlocks

/-! # Chatterjee xi under diagonal localization -/

open MeasureTheory ProbabilityTheory Set Copula.OrdinalSum
open scoped unitInterval

namespace Verification

noncomputable def normalizedSquareMass (C : Copula 2) (v : I) : ℝ :=
  ∫ u : I, normalizedCDF C u v^2

theorem normalizedSquareMass_eq (C : Copula 2) (v : I) :
    normalizedSquareMass C v = ∫ u : I, C.conditionalCDF u v^2 := by
  apply integral_congr_ae
  filter_upwards [normalizedCDF_ae C v] with u hu
  rw [hu]

theorem normalizedSquareMass_measurable (C : Copula 2) : Measurable (normalizedSquareMass C) :=
  ((normalizedCDF_measurable C).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

theorem normalizedSquareMass_integrable (C : Copula 2) : Integrable (normalizedSquareMass C) := by
  change Integrable (fun v => normalizedSquareMass C v)
  simp_rw [normalizedSquareMass_eq]
  exact C.integrable_integral_conditionalCDF_sq

theorem normalizedSquareMass_zero (C : Copula 2) : normalizedSquareMass C 0 = 0 := by
  simp [normalizedSquareMass,normalizedCDF_zero]

theorem normalizedSquareMass_one (C : Copula 2) : normalizedSquareMass C 1 = 1 := by
  simp [normalizedSquareMass,normalizedCDF_one]

theorem normalizedCDF_square_integrable (C : Copula 2) (v : I) :
    Integrable (fun u => normalizedCDF C u v^2) := by
  apply (C.integrable_conditionalCDF_sq v).congr
  filter_upwards [normalizedCDF_ae C v] with u hu
  rw [hu]

theorem conditionalBlocks_squareMass (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) (v : I) :
    (∫ u : I, (conditionalBlocks C D a ha0 ha1).conditionalCDF u v^2) =
      (a : ℝ)*normalizedSquareMass C (lowerCoord a v)+
        (1-(a : ℝ))*normalizedSquareMass D (upperCoord a v) := by
  have he : (fun u => (conditionalBlocks C D a ha0 ha1).conditionalCDF u v^2) =ᵐ[volume]
      unitJoin a (fun u => normalizedCDF C u (lowerCoord a v)^2)
        (fun u => normalizedCDF D u (upperCoord a v)^2) := by
    filter_upwards [conditionalBlocks_conditionalCDF C D a ha0 ha1 v] with u hu
    rw [hu]
    unfold blockKernel unitJoin
    split_ifs <;> rfl
  rw [integral_congr_ae he,integral_unitJoin a ha0 ha1
    (fun u => normalizedCDF C u (lowerCoord a v)^2) (fun u => normalizedCDF D u (upperCoord a v)^2)
    (((normalizedCDF_measurable C).comp (measurable_const.prodMk measurable_id)).pow_const 2)
    (((normalizedCDF_measurable D).comp (measurable_const.prodMk measurable_id)).pow_const 2)
    (normalizedCDF_square_integrable C _) (normalizedCDF_square_integrable D _)]
  rfl

theorem conditionalBlocks_xi (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    (conditionalBlocks C D a ha0 ha1).chatterjeeXi =
      1-(a : ℝ)^2*(1-C.chatterjeeXi)-(1-(a : ℝ))^2*(1-D.chatterjeeXi) := by
  have hi (E : Copula 2) (f : I → I) (hf : Measurable f) :
      Integrable (fun v => normalizedSquareMass E (f v)) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((normalizedSquareMass_measurable E).comp hf).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun v => by
      rw [normalizedSquareMass_eq,Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact (E.integral_conditionalCDF_sq_le (f v)).trans (f v).property.2
  unfold Copula.chatterjeeXi
  simp_rw [conditionalBlocks_squareMass]
  rw [integral_add ((hi C (lowerCoord a) (continuous_lowerCoord a).measurable).const_mul _)
    ((hi D (upperCoord a) (continuous_upperCoord a).measurable).const_mul _),
    integral_const_mul,integral_const_mul,
    integral_lowerCoord a ha0 (normalizedSquareMass C) (normalizedSquareMass_measurable C) (normalizedSquareMass_integrable C),
    integral_upperCoord a ha1 (normalizedSquareMass D) (normalizedSquareMass_measurable D) (normalizedSquareMass_integrable D),
    normalizedSquareMass_one,normalizedSquareMass_zero]
  simp_rw [normalizedSquareMass_eq]
  ring

end Verification
