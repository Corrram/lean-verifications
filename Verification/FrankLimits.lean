import Verification.FrankDensity

open ProbabilityTheory Filter Set
open Copula
open scoped unitInterval Topology

namespace Verification

theorem frank_cdf_lower_bound (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    min (u:ℝ) (v:ℝ)-Real.log 2/θ ≤ (frank θ hθ).cdf ![u,v] := by
  have he : 0 < Real.exp (-θ) := Real.exp_pos _
  have he1 : Real.exp (-θ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1-Real.exp (-θ) := sub_pos.mpr he1
  have hu : Real.exp (-θ) ≤ Real.exp (-θ*(u:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [u.property.2])
  have hv : Real.exp (-θ) ≤ Real.exp (-θ*(v:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [v.property.2])
  have hp := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)
  have hp' := mul_nonneg he.le hd.le
  have hden : frankDen θ u v/(1-Real.exp (-θ)) ≤
      Real.exp (-θ*(u:ℝ))+Real.exp (-θ*(v:ℝ)) := by
    apply (div_le_iff₀ hd).mpr
    unfold frankDen
    nlinarith
  have hu' : Real.exp (-θ*(u:ℝ)) ≤ Real.exp (-θ*min (u:ℝ) (v:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_left (u:ℝ) (v:ℝ)])
  have hv' : Real.exp (-θ*(v:ℝ)) ≤ Real.exp (-θ*min (u:ℝ) (v:ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [min_le_right (u:ℝ) (v:ℝ)])
  have hl := Real.log_le_log (div_pos (frankDen_pos hθ u.property v.property) hd)
    (show frankDen θ u v/(1-Real.exp (-θ)) ≤ 2*Real.exp (-θ*min (u:ℝ) (v:ℝ)) by linarith)
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hl
  rw [← frankRealCDF_eq hθ]
  unfold frankRealCDF
  apply (le_div_iff₀ hθ).mpr
  have hc : (min (u:ℝ) (v:ℝ)-Real.log 2/θ)*θ = θ*min (u:ℝ) (v:ℝ)-Real.log 2 := by
    field_simp
  rw [hc]
  linarith

theorem tendsto_frank_atTop {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, 0 < θ z) (hlim : Tendsto θ l atTop) (u : Fin 2 → I) :
    Tendsto (fun z => (frank (θ z) (hθ z)).cdf u) l (𝓝 ((comonotonic 2).cdf u)) := by
  have hx : u = ![u 0,u 1] := by ext i; fin_cases i <;> rfl
  have hi : Tendsto (fun z => Real.log 2/θ z) l (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop hlim
  have hlo : Tendsto (fun z => min (u 0:ℝ) (u 1:ℝ)-Real.log 2/θ z) l
      (𝓝 ((comonotonic 2).cdf u)) := by
    simpa only [sub_zero, cdf_comonotonic_two] using
      (tendsto_const_nhds (x := min (u 0:ℝ) (u 1:ℝ))).sub hi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · intro z
    have hh := frank_cdf_lower_bound (θ z) (hθ z) (u 0) (u 1)
    simpa only [← hx] using hh
  · intro z
    rw [cdf_comonotonic_two]
    exact le_min ((frank (θ z) (hθ z)).cdf_le_coord u 0)
      ((frank (θ z) (hθ z)).cdf_le_coord u 1)

theorem tendsto_frankNegative_atBot {α : Type*} {l : Filter α} (θ : α → ℝ)
    (hθ : ∀ z, θ z < 0) (hlim : Tendsto θ l atBot) (u : Fin 2 → I) :
    Tendsto (fun z => (frankNegative (θ z) (hθ z)).cdf u) l (𝓝 (countermonotonic.cdf u)) := by
  have hn : Tendsto (fun z => -θ z) l atTop := tendsto_neg_atBot_atTop.comp hlim
  have hh := tendsto_frank_atTop (fun z => -θ z) (fun z => neg_pos.mpr (hθ z)) hn
    ![u 0,unitInterval.symm (u 1)]
  have hs := (tendsto_const_nhds (x := (u 0:ℝ))).sub hh
  have hx : u = ![u 0,u 1] := by ext i; fin_cases i <;> rfl
  have hf (z : α) : (frankNegative (θ z) (hθ z)).cdf u =
      (u 0:ℝ)-(frank (-θ z) (neg_pos.mpr (hθ z))).cdf ![u 0,unitInterval.symm (u 1)] := by
    conv_lhs => rw [hx]
    rw [frankNegative, cdf_reflect_second]
  have ht : (u 0:ℝ)-(comonotonic 2).cdf ![u 0,unitInterval.symm (u 1)] =
      countermonotonic.cdf u := by
    rw [cdf_comonotonic_two, cdf_countermonotonic]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, unitInterval.coe_symm_eq]
    rcases le_total (u 0:ℝ) (1-(u 1:ℝ)) with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right h, max_eq_right (by linarith)]
      ring
  simpa only [hf, ht] using hs

end Verification
