import Copula.Dependence.AMHTotalPositivity

/-! # Ali–Mikhail–Haq CDF TP2 and proved actual-density cases -/

open ProbabilityTheory

namespace Papers.AnsariRockel2024

/-- The zero-parameter AMH copula is independence on the closed square. -/
theorem amh_zero :
    Copula.amh 0 (by norm_num) (by norm_num) = Copula.independence 2 :=
  Copula.amh_zero

/-- CDF-level TP2 holds exactly for nonnegative AMH parameters. -/
theorem amh_cdf_tp2_iff (θ : ℝ) (hmin : -1 ≤ θ) (hmax : θ ≤ 1) :
    (Copula.amh θ hmin hmax).IsTP2CDF ↔ 0 ≤ θ :=
  Copula.isTP2CDF_amh_iff θ hmin hmax

/-- Negative AMH parameters have no MTP2 Lebesgue density. -/
theorem amh_negative_not_mtp2_density (θ : ℝ) (hmin : -1 ≤ θ)
    (hmax : θ ≤ 1) (hθ : θ < 0) :
    ¬(Copula.amh θ hmin hmax).HasMTP2Density :=
  Copula.not_hasMTP2Density_amh_of_neg θ hmin hmax hθ

/-- AMH at θ=0 has the independence MTP2 density. -/
theorem amh_zero_mtp2_density :
    (Copula.amh 0 (by norm_num) (by norm_num)).HasMTP2Density :=
  Copula.hasMTP2Density_amh_zero

/-- AMH at θ=1 has the actual Clayton(1) MTP2 density. -/
theorem amh_one_mtp2_density :
    (Copula.amh 1 (by norm_num) le_rfl).HasMTP2Density :=
  Copula.hasMTP2Density_amh_one

end Papers.AnsariRockel2024
