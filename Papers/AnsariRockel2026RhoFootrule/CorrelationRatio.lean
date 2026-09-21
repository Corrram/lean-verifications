import Papers.AnsariRockel2026RhoFootrule.ExactRegion
import Verification.ConditionalRatioBound

/-! # Theorem 2.6: outer bounds for Chatterjee xi and the copula correlation ratio -/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

/-- The conditional-independent-copy copula in equations (38)--(40). -/
noncomputable abbrev conditionalCopies := Verification.conditionalIID

/-- Variance of the conditional response-rank mean, normalized by the uniform variance. -/
noncomputable abbrev copulaCorrelationRatio := Verification.correlationRatio

/-- Equation (38): the joint distribution of conditional copies. -/
theorem conditional_copies_cdf (C : Copula 2) (u v : I) :
    (conditionalCopies C).cdf ![u, v] =
      ∫ t : I, C.conditionalCDF t u * C.conditionalCDF t v :=
  Verification.conditionalIID_cdf C u v

/-- Equations (39)--(40): both rank coefficients of the actual copy copula. -/
theorem conditional_copies_coefficients (C : Copula 2) :
    (conditionalCopies C).spearmanFootrule = C.chatterjeeXi ∧
      (conditionalCopies C).spearmanRho = copulaCorrelationRatio C :=
  ⟨Verification.conditionalIID_footrule C, Verification.conditionalIID_rho_eq_ratio C⟩

/-- Theorem 2.6, equation (41). No absolute continuity or stochastic monotonicity is assumed. -/
theorem xi_correlationRatio_bounds (C : Copula 2) :
    max 0 (Copula.RankRegion.RhoFootrule.lowerBoundary C.chatterjeeXi) ≤ copulaCorrelationRatio C ∧
      copulaCorrelationRatio C ≤ min (upperRho C.chatterjeeXi) (2 * C.chatterjeeXi) := by
  have hu := sharp_upper_bound (conditionalCopies C)
  have hl := sharp_lower_bound (conditionalCopies C)
  rw [(conditional_copies_coefficients C).1, (conditional_copies_coefficients C).2] at hu hl
  exact ⟨max_le (Verification.correlationRatio_nonneg C) hl,
    le_min hu (Verification.correlationRatio_le_twice_xi C)⟩

/-- Example 2.9: equality in eta <= 2 xi is possible exactly at xi=0. -/
theorem correlationRatio_equality_iff (C : Copula 2) :
    copulaCorrelationRatio C = 2 * C.chatterjeeXi ↔ C.chatterjeeXi = 0 :=
  Verification.correlationRatio_eq_twice_xi_iff C

/-- In particular the outer bound eta=1/2 is unattainable at xi=1/4. -/
theorem quarter_xi_strict_bound (C : Copula 2) (h : C.chatterjeeXi = 1 / 4) :
    copulaCorrelationRatio C < 1 / 2 := by
  have hu := Verification.correlationRatio_le_twice_xi C
  have hn : copulaCorrelationRatio C ≠ 2 * C.chatterjeeXi := by
    intro he
    have hz := (correlationRatio_equality_iff C).mp he
    linarith
  rw [h] at hu hn
  exact lt_of_le_of_ne (by linarith) (by intro he; apply hn; linarith)

end Papers.AnsariRockel2026RhoFootrule
