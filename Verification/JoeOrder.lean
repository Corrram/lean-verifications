import Verification.JoeComparison
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem joe_lowerOrthant_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (joe θ hθ).LowerOrthantLE (joe η hη) := by
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  have hq : 0 < η := lt_of_lt_of_le zero_lt_one hη
  have hr : 1 ≤ η/θ := (le_div_iff₀ hp).mpr (by simpa using hθη)
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, joe_cdf_full θ hθ, joe_cdf_full η hη]
  split_ifs with hz
  · rfl
  have hu : x 0 ≠ 0 := fun h => hz (Or.inl h)
  have hv : x 1 ≠ 0 := fun h => hz (Or.inr h)
  have hbase (u : I) (huz : u ≠ 0) : (1-(u:ℝ))^θ ∈ Ico 0 1 := by
    have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (fun h => huz (Subtype.ext h)))
    exact ⟨Real.rpow_nonneg (sub_nonneg.mpr u.property.2) _,
      Real.rpow_lt_one (sub_nonneg.mpr u.property.2) (by linarith) hp⟩
  have hpow (u : I) : ((1-(u:ℝ))^θ)^(η/θ) = (1-(u:ℝ))^η := by
    rw [← Real.rpow_mul (sub_nonneg.mpr u.property.2)]
    congr 1
    field_simp
  have hi := joe_power_comparison (η/θ) hr (hbase (x 0) hu) (hbase (x 1) hv)
  rw [hpow (x 0), hpow (x 1)] at hi
  have hS0 (p : ℝ) (hp0 : 0 ≤ p) : 0 ≤ (1-(x 0:ℝ))^p+(1-(x 1:ℝ))^p-
      (1-(x 0:ℝ))^p*(1-(x 1:ℝ))^p := by
    have ha0 := Real.rpow_nonneg (sub_nonneg.mpr (x 0).property.2) p
    have hb0 := Real.rpow_nonneg (sub_nonneg.mpr (x 1).property.2) p
    have ha1 := Real.rpow_le_one (sub_nonneg.mpr (x 0).property.2) (by linarith [(x 0).property.1]) hp0
    nlinarith [mul_nonneg hb0 (sub_nonneg.mpr ha1)]
  have hh := Real.rpow_le_rpow (hS0 η hq.le) hi (inv_nonneg.mpr hq.le)
  rw [← Real.rpow_mul (hS0 θ hp.le)] at hh
  have he : (η/θ)*η⁻¹ = θ⁻¹ := by field_simp
  rw [he] at hh
  exact sub_le_sub_left hh 1

theorem joe_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (joe θ hθ).SchurBothLE (joe η hη) := by
  have ho := joe_lowerOrthant_monotone hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (joe_isCI θ hθ).1 (joe_isCI η hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (joe_isCI θ hθ).2 (joe_isCI η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
