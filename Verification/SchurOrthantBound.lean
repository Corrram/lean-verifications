import Verification.StochasticBounds
import Verification.SurvivalOrder

/-! # Schur comparison bounds the CDF by a stochastically monotone comparator -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem convex_hinge (c : ℝ) : ConvexOn ℝ (Icc 0 1) (fun z : ℝ => max (z-c) 0) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul]
  apply max_le
  · have h₁ := mul_le_mul_of_nonneg_left (le_max_left (x-c) 0) ha
    have h₂ := mul_le_mul_of_nonneg_left (le_max_left (y-c) 0) hb
    have he := congrArg (fun z : ℝ => z*c) hab
    nlinarith only [h₁,h₂,he]
  · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))

/-- Lemma 2.6(i): no monotonicity hypothesis is required on the smaller copula. -/
theorem lowerOrthantLE_of_schurLE_isSI (C D : Copula 2) (h : C.SchurLE D) (hD : D.IsSI) :
    C.LowerOrthantLE D := by
  intro x
  let u := x 0
  let v := x 1
  obtain ⟨g,hg,hb,he⟩ := conditionalCDF_antitone_version D hD v
  have hi := integrable_unit_bounded hg.measurable hb
  let φ : ℝ → ℝ := fun z => max (z-g u) 0
  have hc : Continuous φ := by dsimp [φ]; fun_prop
  have hφ := h v φ hc (convex_hinge (g u))
  have hcg := C.integrable_comp_conditionalCDF v hc
  have hprefix : C.cdf ![u,v] - (u:ℝ)*g u ≤ ∫ t : I,φ (C.conditionalCDF t v) := by
    calc
      _ = ∫ t in Iic u, C.conditionalCDF t v-g u := by
        rw [integral_sub (C.integrable_conditionalCDF v).integrableOn (integrable_const _),
          ← C.cdf_eq_integral_conditionalCDF]
        simp [Measure.real,unitInterval.volume_Iic,u.property.1]
      _ ≤ ∫ t in Iic u,φ (C.conditionalCDF t v) := by
        apply setIntegral_mono_on
          ((C.integrable_conditionalCDF v).sub (integrable_const _)).integrableOn
          hcg.integrableOn measurableSet_Iic
        intro t _
        exact le_max_left _ _
      _ ≤ _ := setIntegral_le_integral hcg (Filter.Eventually.of_forall fun _ => le_max_right _ _)
  have hgφ : (fun t : I => φ (g t)) = (Iic u).indicator (fun t => g t-g u) := by
    funext t
    by_cases ht : t ≤ u
    · rw [indicator_of_mem (show t ∈ Iic u from ht)]
      exact max_eq_left (sub_nonneg.mpr (hg ht))
    · rw [indicator_of_notMem (show t ∉ Iic u from ht)]
      exact max_eq_right (sub_nonpos.mpr (hg (le_of_not_ge ht)))
  have hd : (∫ t : I,φ (D.conditionalCDF t v)) = D.cdf ![u,v]-(u:ℝ)*g u := by
    have he' := integral_congr_ae (he.fun_comp φ)
    dsimp only [Function.comp_def] at he'
    rw [he',hgφ,integral_indicator measurableSet_Iic,
      integral_sub hi.integrableOn (integrable_const _)]
    have hgint : (∫ t in Iic u,g t) = D.cdf ![u,v] := by
      rw [D.cdf_eq_integral_conditionalCDF]
      exact integral_congr_ae (ae_restrict_of_ae he.symm)
    rw [hgint]
    simp [Measure.real,unitInterval.volume_Iic,u.property.1]
  rw [hd] at hφ
  have hx : x=![u,v] := by funext i; fin_cases i <;> rfl
  rw [hx]
  linarith

/-- Lemma 2.8(i) follows by reflecting the response coordinate. -/
theorem lowerOrthantLE_of_schurLE_isSD (C D : Copula 2) (h : C.SchurLE D) (hD : D.IsSD) :
    D.LowerOrthantLE C := by
  have hr := lowerOrthantLE_of_schurLE_isSI (C.reflect {1}) (D.reflect {1})
    ((schurLE_reflect_second_iff C D).mpr h) ((Copula.isSI_reflect_second_iff D).mpr hD)
  intro x
  have hh := hr ![x 0,unitInterval.symm (x 1)]
  simp only [Copula.cdf_reflect_second,unitInterval.symm_symm] at hh
  have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  linarith

end Verification
