import Verification.Nelsen11
import Verification.TruncatedPowerConvex

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem nelsen11_isSD (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (nelsen11 θ hθ0 hθ1).IsSD := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen11_zero]
    exact isCD_independence.isSD
  have hp : 0 < θ := lt_of_le_of_ne hθ0 (Ne.symm hz)
  intro a b c v hab hbc
  rcases eq_or_lt_of_le hab with he | hab'
  · subst b; simp
  rcases eq_or_lt_of_le hbc with he | hbc'
  · subst c; simp
  have hv := Real.rpow_le_one v.property.1 v.property.2 hθ0
  have hc := truncatedPower_convex hp (by linarith : θ ≤ 1)
    (show 0 ≤ 2*(1-(v:ℝ)^θ) by linarith) (show 0 < 2-(v:ℝ)^θ by linarith)
  have hs := hc.secant_mono_aux1 a.property.1 c.property.1
    (show (a:ℝ) < b from hab') (show (b:ℝ) < c from hbc')
  have he (x : I) : (nelsen11 θ hθ0 hθ1).cdf ![x,v] =
      (max 0 ((2-(v:ℝ)^θ)*(x:ℝ)^θ-2*(1-(v:ℝ)^θ)))^θ⁻¹ := by
    rw [nelsen11_cdf θ hp hθ1]
    congr 2
    ring
  simp only [he]
  simpa only [add_comm] using hs

theorem nelsen11_isCD (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/2) :
    (nelsen11 θ hθ0 hθ1).IsCD := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen11_zero]
    exact isCD_independence
  have ha : (nelsen11 θ hθ0 hθ1).IsArchimedean := by
    simp only [nelsen11, hz, dite_false, nelsen11Positive]
    exact BivariateGenerator.isArchimedean _
  exact ha.isCD_iff.mpr (nelsen11_isSD θ hθ0 hθ1)

end Verification
