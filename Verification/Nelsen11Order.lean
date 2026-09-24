import Verification.Nelsen11Comparison
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem nelsen11_cdf_compact (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1/2) (u v : I) :
    (nelsen11 θ hθ.le hθ1).cdf ![u,v] =
      (max 0 (2-(2-(u:ℝ)^θ)*(2-(v:ℝ)^θ)))^θ⁻¹ := by
  rw [nelsen11_cdf θ hθ hθ1]
  congr 2
  ring

theorem nelsen11_lowerOrthant_antitone {θ η : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/2) (hθη : θ ≤ η) :
    (nelsen11 η hη0 hη1).LowerOrthantLE (nelsen11 θ hθ0 hθ1) := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen11_zero]
    intro x
    have hh := nelsen11_isNQD η hη0 hη1 (x 0) (x 1)
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    simpa only [← hx, cdf_independence, Fin.prod_univ_two] using hh
  have hp : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hz)
  have hη : 0 < η := hp.trans_le hθη
  have hr : 1 ≤ η/θ := (le_div_iff₀ hp).mpr (by simpa using hθη)
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, nelsen11_cdf_compact η hη hη1, nelsen11_cdf_compact θ hp hθ1]
  have hpow (u : I) : ((u:ℝ)^θ)^(η/θ) = (u:ℝ)^η := by
    rw [← Real.rpow_mul u.property.1]
    congr 1
    field_simp
  have hh := n11_power_comparison (η/θ) hr
    (show (x 0:ℝ)^θ ∈ Icc 0 1 from
      ⟨Real.rpow_nonneg (x 0).property.1 _, Real.rpow_le_one (x 0).property.1 (x 0).property.2 hθ0⟩)
    (show (x 1:ℝ)^θ ∈ Icc 0 1 from
      ⟨Real.rpow_nonneg (x 1).property.1 _, Real.rpow_le_one (x 1).property.1 (x 1).property.2 hθ0⟩)
  rw [hpow (x 0), hpow (x 1)] at hh
  have ht := Real.rpow_le_rpow (le_max_left 0 _) hh (inv_nonneg.mpr hη0)
  rw [← Real.rpow_mul (le_max_left 0 _)] at ht
  have he : (η/θ)*η⁻¹ = θ⁻¹ := by field_simp
  rw [he] at ht
  exact ht

theorem nelsen11_schur_monotone {θ η : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) (hη0 : 0 ≤ η) (hη1 : η ≤ 1/2) (hθη : θ ≤ η) :
    (nelsen11 θ hθ0 hθ1).SchurBothLE (nelsen11 η hη0 hη1) := by
  have ho := nelsen11_lowerOrthant_antitone hθ0 hθ1 hη0 hη1 hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSD _ _
      (nelsen11_isCD θ hθ0 hθ1).1 (nelsen11_isCD η hη0 hη1).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSD _ _
      (nelsen11_isCD θ hθ0 hθ1).2 (nelsen11_isCD η hη0 hη1).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
