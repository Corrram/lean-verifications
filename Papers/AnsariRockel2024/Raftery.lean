import Verification.RafterySource
import Verification.Raftery

open ProbabilityTheory Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- The literal arXiv v3 Table 1 formula fails a necessary copula bound. -/
theorem raftery_printed_cdf_not_copula :
    ¬∃ C : Copula 2, ∀ u v : I,
      C.cdf ![u,v] = Verification.rafteryPrintedCDF (1/2) u v :=
  Verification.raftery_printed_cdf_not_copula

/-- Endpoint consequence of Table 4's independence identity; no interior constructor is assumed. -/
theorem raftery_zero_density {C : Copula 2} (hC : C = independence 2) :
    C.HasMTP2Density := Verification.raftery_zero_density hC

/-- Endpoint consequence of Table 4's comonotonic identity; the zero upper tail excludes it. -/
theorem raftery_one_upperTail {C : Copula 2} (hC : C = comonotonic 2) :
    C.HasUpperTailDependence 1 ∧ ¬C.HasUpperTailDependence 0 :=
  Verification.raftery_one_upperTail hC

/-- Actual copula CDF, with the missing factor 1/(1+delta) restored. -/
theorem raftery_cdf (δ : I) (h1 : δ≠1) (u v : I) :
    (Verification.raftery δ).cdf ![u,v] = min (u:ℝ) v +
      (1-(δ:ℝ))/(1+(δ:ℝ)) * ((u:ℝ)*(v:ℝ))^(1/(1-(δ:ℝ))) *
        (1-(max (u:ℝ) v)^(-(1+(δ:ℝ))/(1-(δ:ℝ)))) :=
  Verification.raftery_cdf_corrected δ h1 u v

theorem raftery_zero : Verification.raftery 0 = independence 2 := Verification.raftery_zero

theorem raftery_one : Verification.raftery 1 = comonotonic 2 := Verification.raftery_one

end Papers.AnsariRockel2024
