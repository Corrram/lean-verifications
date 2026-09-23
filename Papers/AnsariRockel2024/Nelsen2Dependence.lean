import Copula.Dependence.Nelsen2

/-! # Nelsen 2 dependence classification in Ansari–Rockel 2024 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- Table 3: Nelsen 2 is not PQD at any finite admissible parameter. -/
theorem nelsen2_not_pqd (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen2 θ hθ).IsPQD :=
  Copula.not_isPQD_nelsen2 θ hθ

/-- Table 3: no Nelsen 2 member is conditionally increasing. -/
theorem nelsen2_not_ci (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen2 θ hθ).IsCI :=
  Copula.not_isCI_nelsen2 θ hθ

/-- Table 3: parameters strictly above one fail conditional decrease. -/
theorem nelsen2_not_cd (θ : ℝ) (hθ : 1 < θ) :
    ¬(Copula.nelsen2 θ (le_of_lt hθ)).IsCD :=
  Copula.not_isCD_nelsen2 θ hθ

/-- Table 3: the θ=1 lower-Fréchet endpoint is conditionally decreasing. -/
theorem nelsen2_cd_one : (Copula.nelsen2 1 le_rfl).IsCD :=
  Copula.isCD_nelsen2_one

/-- Table 3: the exact conditional-decrease range. -/
theorem nelsen2_cd_iff (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen2 θ hθ).IsCD ↔ θ = 1 :=
  Copula.isCD_nelsen2_iff θ hθ

/-- Table 3: the Nelsen 2 CDF is never TP2. -/
theorem nelsen2_not_tp2_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen2 θ hθ).IsTP2CDF :=
  Copula.not_isTP2CDF_nelsen2 θ hθ

/-- Table 3: no Nelsen 2 member admits an MTP2 Lebesgue density. -/
theorem nelsen2_not_mtp2_density (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.nelsen2 θ hθ).HasMTP2Density :=
  Copula.not_hasMTP2Density_nelsen2 θ hθ

end Papers.AnsariRockel2024