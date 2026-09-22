import Verification.SchurOrthantBound
import Copula.Order.Rank
import Copula.TailDependence.Basic

/-! # General order results, with explicit existence assumptions for tail limits -/

open ProbabilityTheory Verification

namespace Papers.AnsariRockel2024

/-- Proposition 3.2(i), including singular copulas. -/
theorem survival_lowerOrthant_iff (C D : Copula 2) :
    C.LowerOrthantLE D ↔ C.survivalCopula.LowerOrthantLE D.survivalCopula :=
  (lowerOrthantLE_survival_iff C D).symm

/-- Proposition 3.2(ii), for directional conditional increase (CIS). -/
theorem survival_cis_iff (C : Copula 2) : C.IsSI ↔ C.survivalCopula.IsSI :=
  (isSI_survival_iff C).symm

/-- Proposition 3.2(iii), using continuous convex tests of the conditional CDF. -/
theorem survival_schur_iff (C D : Copula 2) :
    C.SchurLE D ↔ C.survivalCopula.SchurLE D.survivalCopula :=
  (schurLE_survival_iff C D).symm

/-- Lemma 2.9 in copula form: both classical concordance coefficients are monotone. -/
theorem concordance_coefficients_mono (C D : Copula 2) (h : C.LowerOrthantLE D) :
    C.spearmanRho ≤ D.spearmanRho ∧ C.kendallTau ≤ D.kendallTau :=
  ⟨h.spearmanRho_le,h.kendallTau_le⟩

/-- The copula specialization of Lemma 2.10, with the stated conditioning direction. -/
theorem schur_xi_mono (C D : Copula 2) (h : C.SchurLE D) :
    C.chatterjeeXi ≤ D.chatterjeeXi := h.chatterjeeXi_le

/-- Lemma 2.12: lower tails, provided both limits exist. -/
theorem lower_tail_mono (C D : Copula 2) (h : C.LowerOrthantLE D) (a b : ℝ)
    (ha : C.HasLowerTailDependence a) (hb : D.HasLowerTailDependence b) : a ≤ b :=
  h.lowerTailDependence_le ha hb

/-- Lemma 2.12: upper tails, provided both limits exist. -/
theorem upper_tail_mono (C D : Copula 2) (h : C.LowerOrthantLE D) (a b : ℝ)
    (ha : C.HasUpperTailDependence a) (hb : D.HasUpperTailDependence b) : a ≤ b :=
  h.upperTailDependence_le ha hb

/-- Lemma 2.6(i): Schur comparison with a CIS copula implies lower orthant comparison. -/
theorem schur_below_cis (C D : Copula 2) (h : C.SchurLE D) (hD : D.IsSI) :
    C.LowerOrthantLE D := lowerOrthantLE_of_schurLE_isSI C D h hD

/-- Lemma 2.8(i): Schur comparison with a CDS copula reverses the orthant direction. -/
theorem schur_below_cds (C D : Copula 2) (h : C.SchurLE D) (hD : D.IsSD) :
    D.LowerOrthantLE C := lowerOrthantLE_of_schurLE_isSD C D h hD

end Papers.AnsariRockel2024
