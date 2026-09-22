import Verification.XiPredictorReflection
import Copula.Order.Schur
import Copula.Order.Orthant
import Copula.Dependence.ConditionalMonotonicity

/-! # Survival invariance of orthant, conditional and Schur orders -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem lowerOrthantLE_survival_iff (C D : Copula 2) :
    C.survivalCopula.LowerOrthantLE D.survivalCopula ↔ C.LowerOrthantLE D := by
  rw [← Copula.concordanceLE_iff_lowerOrthantLE,← Copula.concordanceLE_iff_lowerOrthantLE C D]
  exact Copula.concordanceLE_reflect_iff C D

private theorem isSI_survival_of_isSI (C : Copula 2) (h : C.IsSI) : C.survivalCopula.IsSI := by
  intro a b c v hab hbc
  have hh := h (unitInterval.symm c) (unitInterval.symm b) (unitInterval.symm a)
    (unitInterval.symm v) (unitInterval.symm_le_symm.mpr hbc) (unitInterval.symm_le_symm.mpr hab)
  simp only [Copula.cdf_survivalCopula,unitInterval.coe_symm_eq] at hh ⊢
  nlinarith only [hh]

theorem isSI_survival_iff (C : Copula 2) : C.survivalCopula.IsSI ↔ C.IsSI := by
  constructor
  · intro h
    simpa only [Copula.survivalCopula_survivalCopula] using isSI_survival_of_isSI C.survivalCopula h
  · exact isSI_survival_of_isSI C

private theorem convexOn_response_reflection (φ : ℝ → ℝ) (hφ : ConvexOn ℝ (Icc 0 1) φ) :
    ConvexOn ℝ (Icc 0 1) (fun x => φ (1-x)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hφ.2 (show 1-x ∈ Icc (0:ℝ) 1 by constructor <;> linarith [hx.1,hx.2])
    (show 1-y ∈ Icc (0:ℝ) 1 by constructor <;> linarith [hy.1,hy.2]) ha hb hab
  have he : a*(1-x)+b*(1-y) = 1-(a*x+b*y) := by nlinarith only [hab]
  simpa only [smul_eq_mul,he] using hh

private theorem schurLE_reflect_second_of {C D : Copula 2} (h : C.SchurLE D) :
    (C.reflect {1}).SchurLE (D.reflect {1}) := by
  intro v φ hc hv
  have hh := h (unitInterval.symm v) (fun x => φ (1-x)) (by fun_prop)
    (convexOn_response_reflection φ hv)
  have he (E : Copula 2) : (∫ u : I,φ ((E.reflect {1}).conditionalCDF u v)) =
      ∫ u : I,φ (1-E.conditionalCDF u (unitInterval.symm v)) :=
    integral_congr_ae ((conditionalCDF_reflect_second E v).fun_comp φ)
  rw [he C,he D]
  exact hh

theorem schurLE_reflect_second_iff (C D : Copula 2) :
    (C.reflect {1}).SchurLE (D.reflect {1}) ↔ C.SchurLE D := by
  constructor
  · intro h
    simpa only [Copula.reflect_reflect] using schurLE_reflect_second_of h
  · exact schurLE_reflect_second_of

theorem schurLE_reflect_first_iff (C D : Copula 2) :
    (C.reflect {0}).SchurLE (D.reflect {0}) ↔ C.SchurLE D := by
  have hC := Copula.schurLE_of_rearrangement (C.reflect {0}) C
    unitInterval.measurePreserving_symm (conditionalCDF_reflect_first C)
  have hD := Copula.schurLE_of_rearrangement (D.reflect {0}) D
    unitInterval.measurePreserving_symm (conditionalCDF_reflect_first D)
  exact ⟨fun h => hC.2.trans (h.trans hD.1),fun h => hC.1.trans (h.trans hD.2)⟩

theorem schurLE_survival_iff (C D : Copula 2) :
    C.survivalCopula.SchurLE D.survivalCopula ↔ C.SchurLE D := by
  rw [← Copula.reflect_first_second,← Copula.reflect_first_second,
    schurLE_reflect_second_iff,schurLE_reflect_first_iff]

end Verification
