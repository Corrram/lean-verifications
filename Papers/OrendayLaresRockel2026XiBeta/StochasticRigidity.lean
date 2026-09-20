import Papers.OrendayLaresRockel2026XiBeta.Subclasses
import Verification.StochasticRigidity

/-! # Remark 10: the deterministic boundary in SI and SD classes -/

open ProbabilityTheory

namespace Papers.OrendayLaresRockel2026XiBeta

theorem si_xi_one_iff (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = 1 ↔ C = Copula.comonotonic 2 :=
  Verification.isSI_xi_eq_one_iff C hC

theorem sd_xi_one_iff (C : Copula 2) (hC : C.IsSD) :
    C.chatterjeeXi = 1 ↔ C = Copula.countermonotonic :=
  Verification.isSD_xi_eq_one_iff C hC

theorem si_xi_one_beta (C : Copula 2) (hC : C.IsSI) (hxi : C.chatterjeeXi = 1) :
    C.blomqvistBeta = 1 := by
  rw [(si_xi_one_iff C hC).mp hxi]
  exact Copula.blomqvistBeta_comonotonic

theorem sd_xi_one_beta (C : Copula 2) (hC : C.IsSD) (hxi : C.chatterjeeXi = 1) :
    C.blomqvistBeta = -1 := by
  rw [(sd_xi_one_iff C hC).mp hxi]
  exact Copula.blomqvistBeta_countermonotonic

end Papers.OrendayLaresRockel2026XiBeta
