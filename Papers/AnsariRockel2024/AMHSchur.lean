import Papers.AnsariRockel2024.Dependence
import Papers.AnsariRockel2024.GeneralOrders
import Copula.Order.SymmetricSchur

/-! # Exact AMH Schur order on the two conditional-monotonicity regions -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Table 3: on the nonnegative parameter region, AMH Schur order is parameter order. -/
theorem amh_schur_nonnegative_iff {θ η : ℝ}
    (hθ : 0 ≤ θ) (hθmax : θ ≤ 1)
    (hη : 0 ≤ η) (hηmax : η ≤ 1) :
    (Copula.amh θ (by linarith) hθmax).SchurBothLE
      (Copula.amh η (by linarith) hηmax) ↔ θ ≤ η := by
  let C := Copula.amh θ (by linarith) hθmax
  let D := Copula.amh η (by linarith) hηmax
  have hC : C.IsCI := (amh_ci_iff θ (by linarith) hθmax).2 hθ
  have hD : D.IsCI := (amh_ci_iff η (by linarith) hηmax).2 hη
  rw [Copula.schurBothLE_iff_of_archimedean
    (Copula.isArchimedean_amh θ (by linarith) hθmax)
    (Copula.isArchimedean_amh η (by linarith) hηmax)]
  exact (cis_schur_iff_orthant C D hC.1 hD.1).trans
    (amh_lowerOrthant_iff (by linarith) hθmax (by linarith) hηmax)

/-- Table 3: on the nonpositive region, AMH Schur order reverses parameter order. -/
theorem amh_schur_nonpositive_iff {θ η : ℝ}
    (hθmin : -1 ≤ θ) (hθ : θ ≤ 0)
    (hηmin : -1 ≤ η) (hη : η ≤ 0) :
    (Copula.amh θ hθmin (by linarith)).SchurBothLE
      (Copula.amh η hηmin (by linarith)) ↔ η ≤ θ := by
  let C := Copula.amh θ hθmin (by linarith)
  let D := Copula.amh η hηmin (by linarith)
  have hC : C.IsCD := (amh_cd_iff θ hθmin (by linarith)).2 hθ
  have hD : D.IsCD := (amh_cd_iff η hηmin (by linarith)).2 hη
  rw [Copula.schurBothLE_iff_of_archimedean
    (Copula.isArchimedean_amh θ hθmin (by linarith))
    (Copula.isArchimedean_amh η hηmin (by linarith))]
  exact (cds_schur_iff_reverse_orthant C D hC.1 hD.1).trans
    (amh_lowerOrthant_iff hηmin (by linarith) hθmin (by linarith))

end Papers.AnsariRockel2024
