import Copula.Dependence.NelsenEndpoints

/-! # Table 3 dependence properties at the common Clayton(1) endpoint -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

theorem nelsen12_ci_one : (Copula.nelsen12 1 le_rfl).IsCI :=
  Copula.isCI_nelsen12_one

theorem nelsen14_ci_one : (Copula.nelsen14 1 le_rfl).IsCI :=
  Copula.isCI_nelsen14_one

theorem nelsen12_tp2_cdf_one : (Copula.nelsen12 1 le_rfl).IsTP2CDF :=
  Copula.isTP2CDF_nelsen12_one

theorem nelsen14_tp2_cdf_one : (Copula.nelsen14 1 le_rfl).IsTP2CDF :=
  Copula.isTP2CDF_nelsen14_one

theorem nelsen12_mtp2_density_one : (Copula.nelsen12 1 le_rfl).HasMTP2Density :=
  Copula.hasMTP2Density_nelsen12_one

theorem nelsen14_mtp2_density_one : (Copula.nelsen14 1 le_rfl).HasMTP2Density :=
  Copula.hasMTP2Density_nelsen14_one

theorem nelsen12_not_cd_one : ¬(Copula.nelsen12 1 le_rfl).IsCD :=
  Copula.not_isCD_nelsen12_one

theorem nelsen14_not_cd_one : ¬(Copula.nelsen14 1 le_rfl).IsCD :=
  Copula.not_isCD_nelsen14_one

/-- Nelsen 12 is PQD throughout its full finite parameter range. -/
theorem nelsen12_pqd (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen12 θ hθ).IsPQD :=
  Copula.isPQD_nelsen12 θ hθ

/-- Nelsen 14 is PQD throughout its full finite parameter range. -/
theorem nelsen14_pqd (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen14 θ hθ).IsPQD :=
  Copula.isPQD_nelsen14 θ hθ

/-- Nelsen 12 is never conditionally decreasing. -/
theorem nelsen12_not_cd (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen12 θ hθ).IsCD :=
  Copula.not_isCD_nelsen12 θ hθ

/-- Nelsen 14 is never conditionally decreasing. -/
theorem nelsen14_not_cd (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen14 θ hθ).IsCD :=
  Copula.not_isCD_nelsen14 θ hθ

end Papers.AnsariRockel2024
