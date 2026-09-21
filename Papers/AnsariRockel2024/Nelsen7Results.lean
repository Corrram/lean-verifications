import Papers.AnsariRockel2024.Definitions
import Copula.Order.Nelsen7
import Copula.Rank.ConditionalDerivative

/-! # Nelsen 7: exact conditional law, xi, CI region and Schur parameter order -/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem nelsen7_conditionalCDF (θ v : I) :
    (fun u => (Copula.nelsen7 θ).conditionalCDF u v) =ᵐ[volume]
      fun u => Copula.nelsen7ConditionalCDF θ u v :=
  Copula.conditionalCDF_nelsen7 θ v

theorem nelsen7_derivative (θ v : I) :
    (fun u : I => deriv (Copula.cdfSection (Copula.nelsen7 θ) v) (u : ℝ)) =ᵐ[volume]
      fun u => Copula.nelsen7ConditionalCDF θ u v :=
  ((Copula.nelsen7 θ).conditionalCDF_eq_deriv v).symm.trans (Copula.conditionalCDF_nelsen7 θ v)

theorem nelsen7_xi (θ : I) : (Copula.nelsen7 θ).chatterjeeXi = 1 - (θ : ℝ) :=
  Copula.chatterjeeXi_nelsen7 θ

theorem nelsen7_ci_iff (θ : I) : (Copula.nelsen7 θ).IsCI ↔ θ = 1 :=
  Copula.isCI_nelsen7_iff θ

theorem nelsen7_schur_iff (θ η : I) :
    (Copula.nelsen7 θ).SchurBothLE (Copula.nelsen7 η) ↔ η ≤ θ :=
  Copula.schurBothLE_nelsen7_iff

end Papers.AnsariRockel2024
