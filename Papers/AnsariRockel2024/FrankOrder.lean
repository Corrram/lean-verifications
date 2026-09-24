import Papers.AnsariRockel2024.FrankContinuity
import Verification.FrankOrder
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Verification Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem frank_lowerOrthant_monotone {θ η : ℝ} (hθη : θ ≤ η) :
    (frankSigned θ).LowerOrthantLE (frankSigned η) := by
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  by_cases hθ : θ = 0
  · subst θ
    have hh := ((frank_ci_iff η).mpr hθη).isPQD (x 0) (x 1)
    simpa [frankSigned,cdf_independence,Fin.prod_univ_two] using hh
  by_cases hη : η = 0
  · subst η
    have hh := ((frank_cd_iff θ).mpr hθη).isNQD (x 0) (x 1)
    simpa [frankSigned,cdf_independence,Fin.prod_univ_two] using hh
  rw [frankSigned_cdf_regular,frankSigned_cdf_regular]
  exact frankRegularCDF_monotone_nonzero hθ hη hθη _ _

theorem frank_schur_nonnegative {θ η : ℝ} (hθ : 0 ≤ θ) (hθη : θ ≤ η) :
    (frankSigned θ).SchurBothLE (frankSigned η) := by
  have hc := (frank_ci_iff θ).mpr hθ
  have hd := (frank_ci_iff η).mpr (hθ.trans hθη)
  have ho := frank_lowerOrthant_monotone hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ hc.1 hd.1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ hc.2 hd.2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_transpose,cdf_transpose]
    exact ho ![x 1,x 0]

theorem frank_schur_nonpositive {θ η : ℝ} (hη : η ≤ 0) (hθη : θ ≤ η) :
    (frankSigned η).SchurBothLE (frankSigned θ) := by
  have hc := (frank_cd_iff θ).mpr (hθη.trans hη)
  have hd := (frank_cd_iff η).mpr hη
  have ho := frank_lowerOrthant_monotone hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSD _ _ hd.1 hc.1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSD _ _ hd.2 hc.2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_transpose,cdf_transpose]
    exact ho ![x 1,x 0]

end Papers.AnsariRockel2024
