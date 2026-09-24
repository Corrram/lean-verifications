import Verification.ExtremeValuePickands
import Verification.TawnLimits

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

/-- Table 4's asymmetric logistic Pickands function, identified from the actual copula. -/
theorem tawn_pickands (θ : ℝ) (hθ : 1 ≤ θ) (α β t : I) :
    copulaPickands (tawn θ hθ α β) t =
      (1-(α:ℝ))*(1-(t:ℝ))+(1-(β:ℝ))*(t:ℝ)+
        (((α:ℝ)*(1-(t:ℝ)))^θ+((β:ℝ)*(t:ℝ))^θ)^θ⁻¹ := by
  have hx : 0 ≤ 1-(t:ℝ) := sub_nonneg.mpr t.property.2
  have hy : 0 ≤ (t:ℝ) := t.property.1
  have hu : unitNegExp (1-(t:ℝ)) hx ≠ 0 := by
    intro h
    have hh := congrArg (fun u : I => (u:ℝ)) h
    exact (Real.exp_pos _).ne' hh
  have hv : unitNegExp (t:ℝ) hy ≠ 0 := by
    intro h
    have hh := congrArg (fun u : I => (u:ℝ)) h
    exact (Real.exp_pos _).ne' hh
  have he := extremeValue_exp_coordinates (tawn θ hθ α β)
    (isExtremeValue_tawn θ hθ α β) (1-(t:ℝ)) (t:ℝ) hx hy (by linarith)
  have ht : (⟨(t:ℝ)/(1-(t:ℝ)+(t:ℝ)), div_nonneg hy (by linarith : 0 ≤ 1-(t:ℝ)+(t:ℝ)),
      (div_le_one (by linarith : 0 < 1-(t:ℝ)+(t:ℝ))).mpr (by linarith)⟩ : I) = t := by
    apply Subtype.ext
    simp
  rw [ht] at he
  rw [tawn_cdf_positive θ hθ α β _ _ hu hv] at he
  simp only [unitNegExp,Real.log_exp,neg_neg] at he
  rw [← Real.exp_mul,← Real.exp_mul,← Real.exp_add,← Real.exp_add] at he
  have hi := Real.exp_injective he
  linarith

theorem gumbel_pickands (θ : ℝ) (hθ : 1 ≤ θ) (t : I) :
    copulaPickands (gumbel θ hθ) t = ((1-(t:ℝ))^θ+(t:ℝ)^θ)^θ⁻¹ := by
  simpa only [tawn_one_one,Set.Icc.coe_one,sub_self,zero_mul,zero_add,one_mul] using
    tawn_pickands θ hθ 1 1 t

theorem marshallOlkin_pickands (α β t : I) :
    copulaPickands (marshallOlkin α β) t = 1-min ((α:ℝ)*(1-(t:ℝ))) ((β:ℝ)*(t:ℝ)) := by
  have hx : 0 ≤ 1-(t:ℝ) := sub_nonneg.mpr t.property.2
  have hy : 0 ≤ (t:ℝ) := t.property.1
  have he := extremeValue_exp_coordinates (marshallOlkin α β)
    (isExtremeValue_marshallOlkin α β) (1-(t:ℝ)) (t:ℝ) hx hy (by linarith)
  have ht : (⟨(t:ℝ)/(1-(t:ℝ)+(t:ℝ)), div_nonneg hy (by linarith : 0 ≤ 1-(t:ℝ)+(t:ℝ)),
      (div_le_one (by linarith : 0 < 1-(t:ℝ)+(t:ℝ))).mpr (by linarith)⟩ : I) = t := by
    apply Subtype.ext
    simp
  rw [ht,cdf_marshallOlkin] at he
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,unitNegExp] at he
  simp only [← Real.exp_mul] at he
  by_cases hh : (α:ℝ)*(1-(t:ℝ)) ≤ (β:ℝ)*(t:ℝ)
  · rw [min_eq_left hh]
    rw [min_eq_right (Real.exp_le_exp.mpr (by nlinarith)),← Real.exp_add,← Real.exp_add] at he
    have hi := Real.exp_injective he
    nlinarith
  · have hh' := le_of_not_ge hh
    rw [min_eq_right hh']
    rw [min_eq_left (Real.exp_le_exp.mpr (by nlinarith)),← Real.exp_add,← Real.exp_add] at he
    have hi := Real.exp_injective he
    nlinarith

theorem cuadrasAuge_pickands (α t : I) :
    copulaPickands (cuadrasAuge α) t = 1-(α:ℝ)*min (1-(t:ℝ)) (t:ℝ) := by
  rw [cuadrasAuge,marshallOlkin_pickands,mul_min_of_nonneg _ _ α.property.1]

end Verification
