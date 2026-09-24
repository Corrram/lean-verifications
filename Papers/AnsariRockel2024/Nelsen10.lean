import Verification.Nelsen10Continuity
import Verification.Nelsen10Order

/-! # Tables 1–3: Nelsen 10, its actual CDF, endpoints and dependence exclusions -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen10_cdf (θ u v : I) (hθ : 0 < (θ:ℝ)) :
    (Verification.nelsen10 θ).cdf ![u,v] =
      (u:ℝ)*v/(1+(1-(u:ℝ)^(θ:ℝ))*(1-(v:ℝ)^(θ:ℝ)))^(θ:ℝ)⁻¹ :=
  Verification.nelsen10_cdf θ u v hθ

theorem nelsen10_zero : Verification.nelsen10 0 = Copula.independence 2 :=
  Verification.nelsen10_zero

theorem nelsen10_one : Verification.nelsen10 1 = Copula.amh (-1) le_rfl (by norm_num) :=
  Verification.nelsen10_one

theorem nelsen10_nqd (θ : I) : (Verification.nelsen10 θ).IsNQD :=
  Verification.nelsen10_isNQD θ

theorem nelsen10_pqd_iff (θ : I) : (Verification.nelsen10 θ).IsPQD ↔ θ = 0 :=
  Verification.nelsen10_isPQD_iff θ

theorem nelsen10_ci_iff (θ : I) : (Verification.nelsen10 θ).IsCI ↔ θ = 0 :=
  Verification.nelsen10_isCI_iff θ

theorem nelsen10_density_tp2_iff (θ : I) :
    (Verification.nelsen10 θ).HasMTP2Density ↔ θ = 0 :=
  Verification.nelsen10_density_tp2_iff θ

theorem nelsen10_tails (θ : I) :
    (Verification.nelsen10 θ).HasLowerTailDependence 0 ∧
      (Verification.nelsen10 θ).HasUpperTailDependence 0 :=
  Verification.nelsen10_tails θ

theorem nelsen10_cd (θ : I) : (Verification.nelsen10 θ).IsCD :=
  Verification.nelsen10_isCD θ

theorem nelsen10_continuousAt_zero (u v : I) :
    ContinuousAt (fun θ : I => (Verification.nelsen10 θ).cdf ![u,v]) 0 :=
  Verification.nelsen10_continuousAt_zero u v

theorem nelsen10_cdf_crossing :
    (Verification.nelsen10 Verification.n10Half).cdf ![Verification.n10Low,Verification.n10Low] <
      (Verification.nelsen10 1).cdf ![Verification.n10Low,Verification.n10Low] ∧
    (Verification.nelsen10 1).cdf ![Verification.n10High,Verification.n10High] <
      (Verification.nelsen10 Verification.n10Half).cdf ![Verification.n10High,Verification.n10High] :=
  ⟨Verification.nelsen10_crossing_low, Verification.nelsen10_crossing_high⟩

theorem nelsen10_orthant_incomparable :
    ¬(Verification.nelsen10 Verification.n10Half).LowerOrthantLE (Verification.nelsen10 1) ∧
      ¬(Verification.nelsen10 1).LowerOrthantLE (Verification.nelsen10 Verification.n10Half) :=
  Verification.nelsen10_orthant_incomparable

theorem nelsen10_schur_incomparable :
    ¬(Verification.nelsen10 Verification.n10Half).SchurLE (Verification.nelsen10 1) ∧
      ¬(Verification.nelsen10 1).SchurLE (Verification.nelsen10 Verification.n10Half) :=
  Verification.nelsen10_schur_incomparable

theorem nelsen10_schurBoth_incomparable :
    ¬(Verification.nelsen10 Verification.n10Half).SchurBothLE (Verification.nelsen10 1) ∧
      ¬(Verification.nelsen10 1).SchurBothLE (Verification.nelsen10 Verification.n10Half) :=
  Verification.nelsen10_schurBoth_incomparable

end Papers.AnsariRockel2024
