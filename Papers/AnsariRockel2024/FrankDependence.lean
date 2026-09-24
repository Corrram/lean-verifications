import Verification.FrankDependence

/-! # Table 3: Frank conditional monotonicity and quadrant dependence -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

theorem frank_positive_ci (θ : ℝ) (hθ : 0 < θ) : (Copula.frank θ hθ).IsCI :=
  Verification.frank_positive_isCI θ hθ

theorem frank_positive_not_cd (θ : ℝ) (hθ : 0 < θ) : ¬(Copula.frank θ hθ).IsCD :=
  Verification.frank_positive_not_cd θ hθ

theorem frank_negative_cd (θ : ℝ) (hθ : θ < 0) : (Copula.frankNegative θ hθ).IsCD :=
  Verification.frank_negative_isCD θ hθ

theorem frank_negative_not_ci (θ : ℝ) (hθ : θ < 0) : ¬(Copula.frankNegative θ hθ).IsCI :=
  Verification.frank_negative_not_ci θ hθ

theorem frank_positive_quadrant (θ : ℝ) (hθ : 0 < θ) :
    (Copula.frank θ hθ).IsPQD ∧ ¬(Copula.frank θ hθ).IsNQD :=
  ⟨(frank_positive_ci θ hθ).isPQD, Verification.frank_positive_not_nqd θ hθ⟩

theorem frank_negative_quadrant (θ : ℝ) (hθ : θ < 0) :
    (Copula.frankNegative θ hθ).IsNQD ∧ ¬(Copula.frankNegative θ hθ).IsPQD :=
  ⟨(frank_negative_cd θ hθ).isNQD, Verification.frank_negative_not_pqd θ hθ⟩

theorem frank_negative_not_density_tp2 (θ : ℝ) (hθ : θ < 0) :
    ¬(Copula.frankNegative θ hθ).HasMTP2Density :=
  Verification.frank_negative_not_density_tp2 θ hθ

theorem frank_zero_ci_cd : (Copula.independence 2).IsCI ∧ (Copula.independence 2).IsCD :=
  ⟨Copula.isCI_independence, Copula.isCD_independence⟩

end Papers.AnsariRockel2024
