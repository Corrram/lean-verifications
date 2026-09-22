import Verification.RhoFootruleUniqueness
import Papers.AnsariRockel2026RhoFootrule.ExactRegion

/-! # The unique optimizer of the exact rho--footrule upper boundary -/

open ProbabilityTheory Set

namespace Papers.AnsariRockel2026RhoFootrule

/-- Theorem 1.1 and Proposition 5.8: the arithmetic boundary copula is the only
copula with its footrule and maximal rho, including all contacts and endpoints. -/
theorem boundary_optimizer_unique (a : BoundaryParameter) (C : Copula 2)
    (hp : C.spearmanFootrule = a.footrule) (hr : C.spearmanRho = upperRho a.footrule) :
    C = a.copula :=
  Verification.upper_parameter_copula_unique a C hp (hr.trans (upperRho_parameter a))

/-- At every admissible footrule, exactly one copula attains the upper boundary. -/
theorem upper_boundary_exists_unique (p : ℝ) (hp : p ∈ Icc (-1/2 : ℝ) 1) :
    ∃! C : Copula 2, C.spearmanFootrule = p ∧ C.spearmanRho = upperRho p := by
  obtain ⟨a, ha⟩ := Copula.RankRegion.RhoFootrule.upperParameter_exists hp
  refine ⟨a.copula, ⟨a.coefficients.1.trans ha, ?_⟩, ?_⟩
  · rw [← ha, upperRho_parameter]
    exact a.coefficients.2
  · intro C hC
    exact boundary_optimizer_unique a C (hC.1.trans ha.symm) (ha ▸ hC.2)

/-- Overlapping arcs agree as copulas, not only in their boundary values. -/
theorem boundary_copula_junction (a b : BoundaryParameter) (h : a.footrule = b.footrule) :
    a.copula = b.copula := by
  apply Verification.upper_parameter_copula_unique b a.copula
  · exact a.coefficients.1.trans h
  · exact a.coefficients.2.trans (boundary_value_unique a b h)

end Papers.AnsariRockel2026RhoFootrule
