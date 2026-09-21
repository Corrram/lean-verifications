import Papers.AnsariRockel2026XiRho.RightBoundary
import Verification.XiAffineRegion

/-! # Convexity and fixed-coefficient attainment in the xi region

The full xi=1 boundary supplies the witnesses required by the general
mixture proof. The curved extremal boundary is a separate obligation.
-/

open ProbabilityTheory Set Verification

namespace Papers.AnsariRockel2026XiRho

def attainableRegion : Set (ℝ × ℝ) := xiCoefficientRegion Copula.spearmanRho

private theorem top_witness (C : Copula 2) :
    ∃ D : Copula 2, D.chatterjeeXi = 1 ∧ Copula.spearmanRho D = Copula.spearmanRho C :=
  (xi_one_slice _).mpr (C.spearmanRho_mem_Icc)

/-- All xi values above an attained point occur at the same second coefficient. -/
theorem fixed_coefficient_upward (C : Copula 2) (x : ℝ) (hx : C.chatterjeeXi ≤ x) (hx1 : x ≤ 1) :
    ∃ D : Copula 2, D.chatterjeeXi = x ∧ Copula.spearmanRho D = Copula.spearmanRho C :=
  xi_upward_at_coefficient Copula.spearmanRho Copula.spearmanRho_mix top_witness C x hx hx1

/-- The full attainable region is convex, without assuming boundary attainment or closure. -/
theorem attainable_region_convex : Convex ℝ attainableRegion :=
  convex_xiCoefficientRegion Copula.spearmanRho Copula.spearmanRho_mix top_witness

end Papers.AnsariRockel2026XiRho
