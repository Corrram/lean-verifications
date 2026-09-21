import Verification.XiReflection
import Copula.Rank.Symmetry

/-! # Reflection of the predictor and simultaneous reflection preserve xi -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem integral_reflected_Iic (f : I → ℝ) (hf : Integrable f) (u : I) :
    (∫ t in Iic u, f (unitInterval.symm t)) = (∫ t : I, f t) - ∫ t in Iic (unitInterval.symm u), f t := by
  have he : unitInterval.symm ⁻¹' Ici (unitInterval.symm u) = Iic u := by
    ext t
    simp only [mem_preimage, mem_Ici, mem_Iic, unitInterval.symm_le_symm]
  have h := unitInterval.measurePreserving_symm.setIntegral_preimage_emb
    unitInterval.symmMeasurableEquiv.measurableEmbedding f (Ici (unitInterval.symm u))
  rw [he, integral_Ici_eq_integral_Ioi] at h
  rw [h]
  simpa only [compl_Iic] using (setIntegral_compl (s := Iic (unitInterval.symm u)) measurableSet_Iic hf)

theorem conditionalCDF_reflect_first (C : Copula 2) (v : I) :
    (fun u => (C.reflect {0}).conditionalCDF u v) =ᵐ[volume]
      fun u => C.conditionalCDF (unitInterval.symm u) v := by
  apply Copula.conditionalCDF_ae_eq_of_integral _ v
    (unitInterval.measurePreserving_symm.integrable_comp_of_integrable (C.integrable_conditionalCDF v))
    (fun u => C.conditionalCDF_nonneg _ _) _
  intro u
  dsimp only [Function.comp_def]
  rw [integral_reflected_Iic _ (C.integrable_conditionalCDF v), C.integral_conditionalCDF,
    ← C.cdf_eq_integral_conditionalCDF, C.cdf_reflect_first]

theorem xi_reflect_first (C : Copula 2) : (C.reflect {0}).chatterjeeXi = C.chatterjeeXi := by
  unfold Copula.chatterjeeXi
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    have he := integral_congr_ae ((conditionalCDF_reflect_first C v).fun_comp (fun r : ℝ => r ^ 2))
    dsimp only [Function.comp_def] at he ⊢
    rw [he]
    exact unitInterval.measurePreserving_symm.integral_comp
      unitInterval.symmMeasurableEquiv.measurableEmbedding (fun u : I => C.conditionalCDF u v ^ 2)

theorem xi_survival (C : Copula 2) : C.survivalCopula.chatterjeeXi = C.chatterjeeXi := by
  rw [← Copula.reflect_first_second, xi_reflect_second, xi_reflect_first]

end Verification
