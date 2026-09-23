import Copula.Dependence.GenestGhoudi

/-! # Genest–Ghoudi dependence properties from Table 3 -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- The actual family never has positive quadrant dependence. -/
theorem genestGhoudi_not_pqd (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.genestGhoudi θ hθ).IsPQD :=
  Copula.not_isPQD_genestGhoudi θ hθ

/-- No finite family member is conditionally increasing. -/
theorem genestGhoudi_not_ci (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.genestGhoudi θ hθ).IsCI :=
  Copula.not_isCI_genestGhoudi θ hθ

/-- CD holds exactly at the countermonotonic endpoint. -/
theorem genestGhoudi_cd_iff (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.genestGhoudi θ hθ).IsCD ↔ θ = 1 :=
  Copula.isCD_genestGhoudi_iff θ hθ

/-- The actual CDF is not TP2 at any finite admissible parameter. -/
theorem genestGhoudi_not_tp2_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.genestGhoudi θ hθ).IsTP2CDF :=
  Copula.not_isTP2CDF_genestGhoudi θ hθ

/-- The actual copula admits no MTP2 Lebesgue density. -/
theorem genestGhoudi_not_mtp2_density (θ : ℝ) (hθ : 1 ≤ θ) :
    ¬(Copula.genestGhoudi θ hθ).HasMTP2Density :=
  Copula.not_hasMTP2Density_genestGhoudi θ hθ

end Papers.AnsariRockel2024
