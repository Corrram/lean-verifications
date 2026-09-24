import Verification.GumbelBarnettDependence

/-! # Tables 1–3: Gumbel–Barnett on its full closed parameter interval -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem gumbelBarnett_cdf (θ u v : I) :
    (Verification.gumbelBarnett θ).cdf ![u,v] =
      (u:ℝ)*v*Real.exp (-(θ:ℝ)*Real.log (u:ℝ)*Real.log (v:ℝ)) :=
  Verification.gumbelBarnett_cdf θ u v

theorem gumbelBarnett_zero : Verification.gumbelBarnett 0 = Copula.independence 2 :=
  Verification.gumbelBarnett_zero

theorem gumbelBarnett_parameter_continuous (u v : I) :
    Continuous (fun θ : I => (Verification.gumbelBarnett θ).cdf ![u,v]) :=
  Verification.gumbelBarnett_cdf_parameter_continuous u v

theorem gumbelBarnett_cd (θ : I) : (Verification.gumbelBarnett θ).IsCD :=
  Verification.gumbelBarnett_isCD θ

theorem gumbelBarnett_ci_iff (θ : I) : (Verification.gumbelBarnett θ).IsCI ↔ θ = 0 :=
  Verification.gumbelBarnett_isCI_iff θ

theorem gumbelBarnett_density_tp2_iff (θ : I) :
    (Verification.gumbelBarnett θ).HasMTP2Density ↔ θ = 0 :=
  Verification.gumbelBarnett_density_tp2_iff θ

theorem gumbelBarnett_lowerOrthant_iff (θ η : I) :
    (Verification.gumbelBarnett θ).LowerOrthantLE (Verification.gumbelBarnett η) ↔ η ≤ θ :=
  Verification.gumbelBarnett_lowerOrthant_iff θ η

theorem gumbelBarnett_schur_iff (θ η : I) :
    (Verification.gumbelBarnett θ).SchurBothLE (Verification.gumbelBarnett η) ↔ θ ≤ η :=
  Verification.gumbelBarnett_schur_iff θ η

theorem gumbelBarnett_tails (θ : I) :
    (Verification.gumbelBarnett θ).HasLowerTailDependence 0 ∧
      (Verification.gumbelBarnett θ).HasUpperTailDependence 0 :=
  Verification.gumbelBarnett_tails θ

end Papers.AnsariRockel2024
