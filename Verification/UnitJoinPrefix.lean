import Verification.UnitSplit

/-! # Prefix integration for tagged predictor blocks -/

open MeasureTheory ProbabilityTheory Set Copula.OrdinalSum
open scoped unitInterval

namespace Verification

theorem upperEmbed_le_iff_ae (a r : I) (ha : a < 1) :
    ∀ᵐ u : I, upperEmbed a u ≤ r ↔ u ≤ upperCoord a r := by
  by_cases hr : a ≤ r
  · exact Filter.Eventually.of_forall fun u => upperEmbed_le_iff a u r ha hr
  filter_upwards [Measure.ae_ne (volume : Measure I) 0] with u hu
  rw [upperCoord_of_le a r (le_of_not_ge hr)]
  have hn : ¬ upperEmbed a u ≤ r := fun h => hr ((le_upperEmbed a u).trans h)
  have hu' : ¬ u ≤ 0 := fun h => hu (le_antisymm h u.property.1)
  exact iff_of_false hn hu'

theorem integral_unitJoin_prefix (a : I) (ha0 : 0 < a) (ha1 : a < 1)
    (f g : I → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable f) (hj : Integrable g) (r : I) :
    (∫ u in Iic r, unitJoin a f g u) =
      (a : ℝ)*(∫ u in Iic (lowerCoord a r), f u)+
        (1-(a : ℝ))*(∫ u in Iic (upperCoord a r), g u) := by
  classical
  let F := (Iic r).indicator (unitJoin a f g)
  have hL : (fun u => F (lowerEmbed a u)) = (Iic (lowerCoord a r)).indicator f := by
    funext u
    simp only [F,Set.indicator,mem_Iic,lowerEmbed_le_iff a u r ha0,unitJoin_lower a ha0]
  have hU : (fun u => F (upperEmbed a u)) =ᵐ[volume] (Iic (upperCoord a r)).indicator g := by
    filter_upwards [unitJoin_upper a ha1 f g,upperEmbed_le_iff_ae a r ha1] with u hu hr
    simp only [F,Set.indicator,mem_Iic,hr,hu]
  have hFi := hi.indicator (s := Iic (lowerCoord a r)) measurableSet_Iic
  have hGi := hj.indicator (s := Iic (upperCoord a r)) measurableSet_Iic
  rw [← integral_indicator measurableSet_Iic]
  change (∫ u : I, F u) = _
  rw [integral_unit_split a F ((measurable_unitJoin a hf hg).indicator measurableSet_Iic)
    (by rw [hL]; exact hFi) (hGi.congr hU.symm),hL,integral_congr_ae hU,
    integral_indicator measurableSet_Iic,integral_indicator measurableSet_Iic]

end Verification
