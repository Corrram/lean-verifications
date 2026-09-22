import Copula.Dependence.Density
import Mathlib.MeasureTheory.Integral.Prod

/-! # Fubini for lower orthants of the bivariate unit cube -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem integral_cube_Iic_iterated {f : (Fin 2 → I) → ℝ} (hf : Integrable f) (u v : I) :
    (∫ x in Iic ![u,v], f x) = ∫ s in Iic u, ∫ t in Iic v, f ![s,t] := by
  have hm := (volume_preserving_finTwoArrow I).symm MeasurableEquiv.finTwoArrow
  have he := hm.setIntegral_preimage_emb MeasurableEquiv.finTwoArrow.symm.measurableEmbedding f (Iic ![u,v])
  have hs : MeasurableEquiv.finTwoArrow.symm ⁻¹' Iic ![u,v] = Iic u ×ˢ Iic v := by
    ext p
    change (∀ i : Fin 2, (![p.1,p.2] i) ≤ ![u,v] i) ↔ p.1 ≤ u ∧ p.2 ≤ v
    simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hs] at he
  rw [← he]
  have hi := hm.integrable_comp_of_integrable hf
  exact setIntegral_prod _ hi.integrableOn

end Verification
