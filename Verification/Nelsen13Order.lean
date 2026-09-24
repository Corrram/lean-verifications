import Verification.Nelsen13
import Verification.GumbelBarnettDependence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem n13_power_comparison (r : ℝ) (hr : 1 ≤ r) {a b : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) : a^r+b^r-1 ≤ (a+b-1)^r := by
  rcases eq_or_lt_of_le ha with he | ha'
  · subst a; simp
  rcases eq_or_lt_of_le hb with he | hb'
  · subst b; simp
  have hc := convexOn_rpow hr
  have h1 : (1:ℝ) ∈ Ici 0 := by norm_num
  have hab : a+b-1 ∈ Ici 0 := by change 0 ≤ a+b-1; linarith
  have hA := hc.secant_mono_aux1 h1 hab ha' (by linarith : a < a+b-1)
  have hB := hc.secant_mono_aux1 h1 hab hb' (by linarith : b < a+b-1)
  simp only [Real.one_rpow] at hA hB
  nlinarith

theorem nelsen13_lowerOrthant_monotone_pos {θ η : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hθη : θ ≤ η) :
    (nelsen13 θ hθ.le).LowerOrthantLE (nelsen13 η hη.le) := by
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, nelsen13_cdf θ hθ, nelsen13_cdf η hη]
  split_ifs with hz
  · rfl
  apply Real.exp_le_exp.mpr
  apply sub_le_sub_left
  have hbase (u : I) : 0 ≤ 1-Real.log (u:ℝ) := le_trans zero_le_one (n13_inv_base u)
  have hp (u : I) : 1 ≤ (1-Real.log (u:ℝ))^θ := Real.one_le_rpow (n13_inv_base u) hθ.le
  have hpow (u : I) : ((1-Real.log (u:ℝ))^θ)^(η/θ) = (1-Real.log (u:ℝ))^η := by
    rw [← Real.rpow_mul (hbase u)]
    congr 1
    field_simp
  have hh := n13_power_comparison (η/θ) ((le_div_iff₀ hθ).mpr (by simpa using hθη))
    (hp (x 0)) (hp (x 1))
  rw [hpow (x 0), hpow (x 1)] at hh
  have hηbase : 0 ≤ (1-Real.log (x 0:ℝ))^η+(1-Real.log (x 1:ℝ))^η-1 := by
    linarith [Real.one_le_rpow (n13_inv_base (x 0)) hη.le,
      Real.one_le_rpow (n13_inv_base (x 1)) hη.le]
  have hθbase : 0 ≤ (1-Real.log (x 0:ℝ))^θ+(1-Real.log (x 1:ℝ))^θ-1 := by
    linarith [hp (x 0), hp (x 1)]
  have ht := Real.rpow_le_rpow hηbase hh (inv_nonneg.mpr hη.le)
  rw [← Real.rpow_mul hθbase] at ht
  have he : (η/θ)*η⁻¹ = θ⁻¹ := by field_simp
  rwa [he] at ht

theorem nelsen13_zero_lowerOrthant (θ : ℝ) (hθ : 0 < θ) :
    (nelsen13 0 le_rfl).LowerOrthantLE (nelsen13 θ hθ.le) := by
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [nelsen13_zero, hx, gumbelBarnett_cdf, nelsen13_cdf θ hθ]
  by_cases hu : x 0 = 0
  · simp [hu]
  by_cases hv : x 1 = 0
  · simp [hv]
  simp only [hu, hv, or_self, ite_false]
  have hu0 : 0 < (x 0:ℝ) := lt_of_le_of_ne (x 0).property.1 (Ne.symm (fun h => hu (Subtype.ext h)))
  have hv0 : 0 < (x 1:ℝ) := lt_of_le_of_ne (x 1).property.1 (Ne.symm (fun h => hv (Subtype.ext h)))
  have hA := Real.one_le_rpow (n13_inv_base (x 0)) hθ.le
  have hB := Real.one_le_rpow (n13_inv_base (x 1)) hθ.le
  have hh : (1-Real.log (x 0:ℝ))^θ+(1-Real.log (x 1:ℝ))^θ-1 ≤
      (1-Real.log (x 0:ℝ))^θ*(1-Real.log (x 1:ℝ))^θ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)]
  have hA0 : 0 ≤ 1-Real.log (x 0:ℝ) := le_trans zero_le_one (n13_inv_base (x 0))
  have hB0 : 0 ≤ 1-Real.log (x 1:ℝ) := le_trans zero_le_one (n13_inv_base (x 1))
  have ht := Real.rpow_le_rpow (show 0 ≤ (1-Real.log (x 0:ℝ))^θ+(1-Real.log (x 1:ℝ))^θ-1 by linarith)
    hh (inv_nonneg.mpr hθ.le)
  rw [Real.mul_rpow (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _),
    Real.rpow_rpow_inv hA0 hθ.ne', Real.rpow_rpow_inv hB0 hθ.ne'] at ht
  have he : (x 0:ℝ)*(x 1:ℝ)*Real.exp (-((1:I):ℝ)*Real.log (x 0:ℝ)*Real.log (x 1:ℝ)) =
      Real.exp (1-(1-Real.log (x 0:ℝ))*(1-Real.log (x 1:ℝ))) := by
    rw [show 1-(1-Real.log (x 0:ℝ))*(1-Real.log (x 1:ℝ)) =
      Real.log (x 0:ℝ)+Real.log (x 1:ℝ)-Real.log (x 0:ℝ)*Real.log (x 1:ℝ) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_log hu0, Real.exp_log hv0]
    simp [Real.exp_neg, div_eq_mul_inv]
  rw [he]
  exact Real.exp_le_exp.mpr (sub_le_sub_left ht 1)

theorem nelsen13_lowerOrthant_monotone {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (nelsen13 θ hθ).LowerOrthantLE (nelsen13 η hη) := by
  by_cases hz : θ = 0
  · subst θ
    by_cases he : η = 0
    · subst η; exact fun _ => le_rfl
    · exact nelsen13_zero_lowerOrthant η (lt_of_le_of_ne hη (Ne.symm he))
  · exact nelsen13_lowerOrthant_monotone_pos (lt_of_le_of_ne hθ (Ne.symm hz))
      (lt_of_lt_of_le (lt_of_le_of_ne hθ (Ne.symm hz)) hθη) hθη

end Verification
