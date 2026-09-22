import Verification.UnitJoinPrefix
import Verification.ConditionalBlocksXi
import Verification.ConditionalBlocksRatio

/-! # Identification with package ordinal sums and exact directional coefficients -/

open MeasureTheory ProbabilityTheory Set Copula.OrdinalSum
open scoped unitInterval

namespace Verification

theorem normalizedCDF_prefix (C : Copula 2) (u v : I) :
    (∫ t in Iic u, normalizedCDF C t v) = C.cdf ![u,v] := by
  rw [integral_congr_ae (ae_restrict_of_ae (normalizedCDF_ae C v)),C.cdf_eq_integral_conditionalCDF]

theorem conditionalBlocks_eq_ordinalSum (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    conditionalBlocks C D a ha0 ha1 = C.ordinalSum D a := by
  apply Copula.cdf_injective
  funext z
  have hz : z = ![z 0,z 1] := by funext i; fin_cases i <;> rfl
  rw [hz]
  change (copulaOfConditionalAE _ _ _ _ _ _).cdf ![z 0,z 1] = _
  rw [copulaOfConditionalAE_cdf,Copula.cdf_ordinalSum]
  simp only [blockKernel]
  rw [integral_unitJoin_prefix a ha0 ha1
    (fun t => normalizedCDF C t (lowerCoord a (z 1))) (fun t => normalizedCDF D t (upperCoord a (z 1)))
    ((normalizedCDF_measurable C).comp (measurable_const.prodMk measurable_id))
    ((normalizedCDF_measurable D).comp (measurable_const.prodMk measurable_id))
    (normalizedCDF_integrable C _) (normalizedCDF_integrable D _),normalizedCDF_prefix,normalizedCDF_prefix]
  rfl

theorem chatterjeeXi_ordinalSum (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).chatterjeeXi =
      1-(a : ℝ)^2*(1-C.chatterjeeXi)-(1-(a : ℝ))^2*(1-D.chatterjeeXi) := by
  by_cases ha0 : a = 0
  · subst a; simp
  by_cases ha1 : a = 1
  · subst a; simp
  have h0 : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
  have h1 : a < 1 := lt_of_le_of_ne a.property.2 ha1
  rw [← conditionalBlocks_eq_ordinalSum C D a h0 h1]
  exact conditionalBlocks_xi C D a h0 h1

theorem correlationRatio_ordinalSum (C D : Copula 2) (a : I) :
    correlationRatio (C.ordinalSum D a) =
      1-(a : ℝ)^3*(1-correlationRatio C)-(1-(a : ℝ))^3*(1-correlationRatio D) := by
  by_cases ha0 : a = 0
  · subst a; simp
  by_cases ha1 : a = 1
  · subst a; simp
  have h0 : 0 < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
  have h1 : a < 1 := lt_of_le_of_ne a.property.2 ha1
  rw [← conditionalBlocks_eq_ordinalSum C D a h0 h1]
  exact conditionalBlocks_correlationRatio C D a h0 h1

end Verification
