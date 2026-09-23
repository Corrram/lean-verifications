import Copula.Dependence.Nelsen8

/-! # Nelsen 8 dependence exclusions in Ansari–Rockel 2024 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- Table 3 support: every Nelsen 8 member fails positive quadrant dependence. -/
theorem nelsen8_not_pqd (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen8 θ hθ).IsPQD :=
  Copula.not_isPQD_nelsen8 θ hθ

/-- Table 3: no Nelsen 8 member is conditionally increasing. -/
theorem nelsen8_not_ci (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen8 θ hθ).IsCI :=
  Copula.not_isCI_nelsen8 θ hθ

/-- Table 3: the Nelsen 8 CDF is never TP2. -/
theorem nelsen8_not_tp2_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen8 θ hθ).IsTP2CDF :=
  Copula.not_isTP2CDF_nelsen8 θ hθ

/-- Table 3: no Nelsen 8 member admits an MTP2 density. -/
theorem nelsen8_not_mtp2_density (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen8 θ hθ).HasMTP2Density :=
  Copula.not_hasMTP2Density_nelsen8 θ hθ

/-- Table 3: the θ=1 lower-Fréchet member is conditionally decreasing. -/
theorem nelsen8_cd_one : (Copula.nelsen8 1 le_rfl).IsCD :=
  Copula.isCD_nelsen8_one

end Papers.AnsariRockel2024