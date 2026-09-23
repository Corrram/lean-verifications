import Copula.Dependence.NelsenEndpoints
import Copula.Dependence.GumbelTotalPositivity
import Copula.Dependence.MaxProductTotalPositivity

/-! # CDF-level TP2 for named Table 3 and 5 families

These are statements about the actual copula CDF. They do not assert MTP2
of a Lebesgue density, which is a separate property in the article.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen12_tp2_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen12 θ hθ).IsTP2CDF :=
  Copula.isTP2CDF_nelsen12 θ hθ

theorem nelsen14_tp2_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.nelsen14 θ hθ).IsTP2CDF :=
  Copula.isTP2CDF_nelsen14 θ hθ

theorem gumbel_tp2_cdf (θ : ℝ) (hθ : 1 ≤ θ) :
    (Copula.gumbel θ hθ).IsTP2CDF :=
  Copula.isTP2CDF_gumbel θ hθ

theorem tawn_tp2_cdf (θ : ℝ) (hθ : 1 ≤ θ) (α β : I) :
    (Copula.tawn θ hθ α β).IsTP2CDF :=
  Copula.isTP2CDF_tawn θ hθ α β

theorem marshallOlkin_tp2_cdf (α β : I) :
    (Copula.marshallOlkin α β).IsTP2CDF :=
  Copula.isTP2CDF_marshallOlkin α β

theorem cuadrasAuge_tp2_cdf (α : I) :
    (Copula.cuadrasAuge α).IsTP2CDF :=
  Copula.isTP2CDF_cuadrasAuge α

end Papers.AnsariRockel2024
