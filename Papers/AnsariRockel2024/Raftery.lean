import Verification.RafterySource
import Verification.Raftery
import Verification.RafteryTails
import Verification.RafteryLimits

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

theorem raftery_tails_lt_one (δ : I) (h1 : δ≠1) :
    (Verification.raftery δ).HasLowerTailDependence (2*(δ:ℝ)/(1+(δ:ℝ))) ∧
      (Verification.raftery δ).HasUpperTailDependence 0 :=
  Verification.raftery_tails_lt_one δ h1

theorem raftery_tails_one :
    (Verification.raftery 1).HasLowerTailDependence 1 ∧
      (Verification.raftery 1).HasUpperTailDependence 1 := Verification.raftery_tails_one

theorem raftery_comonotonic_bounds (δ u v : I) :
    min (u:ℝ) v-(1-(δ:ℝ)) ≤ (Verification.raftery δ).cdf ![u,v] ∧
      (Verification.raftery δ).cdf ![u,v] ≤ min (u:ℝ) v :=
  Verification.raftery_comonotonic_bounds δ u v

theorem raftery_tendsto_parameter {A : Type*} {l : Filter A} (δ : A → I) (η : I)
    (hδ : Filter.Tendsto (fun x => (δ x:ℝ)) l (nhds (η:ℝ))) (u v : I) :
    Filter.Tendsto (fun x => (Verification.raftery (δ x)).cdf ![u,v]) l
      (nhds ((Verification.raftery η).cdf ![u,v])) :=
  Verification.raftery_tendsto_parameter δ η hδ u v

theorem raftery_tendsto_zero {A : Type*} {l : Filter A} (δ : A → I)
    (hδ : Filter.Tendsto (fun x => (δ x:ℝ)) l (nhds 0)) (u v : I) :
    Filter.Tendsto (fun x => (Verification.raftery (δ x)).cdf ![u,v]) l
      (nhds ((independence 2).cdf ![u,v])) := Verification.raftery_tendsto_zero δ hδ u v

theorem raftery_tendsto_one {A : Type*} {l : Filter A} (δ : A → I)
    (hδ : Filter.Tendsto (fun x => (δ x:ℝ)) l (nhds 1)) (u v : I) :
    Filter.Tendsto (fun x => (Verification.raftery (δ x)).cdf ![u,v]) l
      (nhds ((comonotonic 2).cdf ![u,v])) := Verification.raftery_tendsto_one δ hδ u v

end Papers.AnsariRockel2024
