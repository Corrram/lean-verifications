import Verification.FootruleAbsolute
import Papers.Rockel2026XiFootrule.RegionGeometry
import Papers.AnsariRockel2026XiRho.RegionGeometry
import Verification.XiReflection

/-! # Additional results in the JCAM resubmission

Proposition 3.4 and Corollaries 3.5--3.6 are absent from arXiv v1.
The source is recorded by filename and hash in SOURCE_COMPARISON.md.
-/

open ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

/-- The mirrored relaxed curve lies strictly below the square-root curve. -/
theorem relaxed_mirrored_bound (μ : ℝ) (hμ : μ ∈ Ioc 0 2) :
    -relaxedFootrule μ < Real.sqrt (relaxedXi μ) := by
  have h := relaxed_footrule_sq_lt_xi μ hμ
  have hn : 0 ≤ relaxedXi μ := (sq_nonneg _).trans h.le
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (relaxedXi μ)]

/-- The absolute bound is strict whenever footrule is negative. -/
theorem negative_footrule_strict (C : Copula 2) (hC : C.spearmanFootrule < 0) :
    |C.spearmanFootrule| < Real.sqrt C.chatterjeeXi := by
  rw [abs_of_neg hC]
  have h := negative_footrule_sq_lt_xi C hC
  nlinarith [Real.sq_sqrt C.chatterjeeXi_nonneg, Real.sqrt_nonneg C.chatterjeeXi]

/-- Absolute version of the upper bound, for every copula. -/
theorem abs_footrule_le_sqrt_xi (C : Copula 2) :
    |C.spearmanFootrule| ≤ Real.sqrt C.chatterjeeXi := by
  by_cases h : 0 ≤ C.spearmanFootrule
  · simpa only [abs_of_nonneg h] using footrule_le_sqrt_xi C
  · exact (negative_footrule_strict C (lt_of_not_ge h)).le

/-- The equality cases are exactly the nonnegative Frechet mixtures. -/
theorem abs_footrule_eq_sqrt_xi_iff (C : Copula 2) :
    |C.spearmanFootrule| = Real.sqrt C.chatterjeeXi ↔
      ∃ a : I, C = upperBoundary a := by
  constructor
  · intro h
    have hn : 0 ≤ C.spearmanFootrule := by
      by_contra hh
      exact (ne_of_lt (negative_footrule_strict C (lt_of_not_ge hh))) h
    rw [abs_of_nonneg hn] at h
    exact ⟨boundaryParameter ⟨C.chatterjeeXi,C.chatterjeeXi_mem_Icc⟩,
      (upperBoundary_unique ⟨C.chatterjeeXi,C.chatterjeeXi_mem_Icc⟩ C rfl).mp h⟩
  · rintro ⟨a,rfl⟩
    rw [footrule_upperBoundary, xi_upperBoundary, Real.sqrt_sq_eq_abs]

private theorem footrule_sq_le_xi (C : Copula 2) :
    C.spearmanFootrule ^ 2 ≤ C.chatterjeeXi := by
  have h := abs_footrule_le_sqrt_xi C
  nlinarith [sq_abs C.spearmanFootrule, Real.sq_sqrt C.chatterjeeXi_nonneg,
    Real.sqrt_nonneg C.chatterjeeXi, abs_nonneg C.spearmanFootrule]

private theorem frechet_rho (a : I) : (upperBoundary a).spearmanRho = (a : ℝ) := by
  simp [upperBoundary, Copula.spearmanRho_mix]

/-- Each footrule pair is attained as a rho pair by an actual copula. -/
theorem footrule_pair_attained_as_rho (C : Copula 2) :
    ∃ D : Copula 2, D.chatterjeeXi = C.chatterjeeXi ∧ D.spearmanRho = C.spearmanFootrule := by
  by_cases hy : 0 ≤ C.spearmanFootrule
  · let a : I := ⟨C.spearmanFootrule,hy,C.spearmanFootrule_mem_Icc.2⟩
    obtain ⟨D,hx,hr⟩ := Papers.AnsariRockel2026XiRho.fixed_coefficient_upward
      (upperBoundary a) C.chatterjeeXi
      (by simpa only [xi_upperBoundary, a] using footrule_sq_le_xi C) C.chatterjeeXi_mem_Icc.2
    exact ⟨D,hx,hr.trans (frechet_rho a)⟩
  · let a : I := ⟨-C.spearmanFootrule,by linarith,
      by linarith [C.spearmanFootrule_mem_Icc.1]⟩
    obtain ⟨D,hx,hr⟩ := Papers.AnsariRockel2026XiRho.fixed_coefficient_upward
      ((upperBoundary a).reflect {1}) C.chatterjeeXi
      (by simpa only [xi_reflect_second, xi_upperBoundary, a, neg_sq] using footrule_sq_le_xi C)
      C.chatterjeeXi_mem_Icc.2
    refine ⟨D,hx,?_⟩
    rw [hr, Copula.spearmanRho_reflect_second, frechet_rho]
    exact neg_neg _

/-- Strict containment of the entire attained regions; W supplies a missing pair. -/
theorem footrule_region_ssubset_rho_region :
    attainableRegion ⊂ Papers.AnsariRockel2026XiRho.attainableRegion := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · rintro ⟨x,y⟩ ⟨C,hx,hy⟩
    obtain ⟨D,hd,hr⟩ := footrule_pair_attained_as_rho C
    exact ⟨D,hd.trans hx,hr.trans hy⟩
  · intro he
    have hw : ((1,-1) : ℝ × ℝ) ∈ Papers.AnsariRockel2026XiRho.attainableRegion :=
      ⟨Copula.countermonotonic, by simp, by simp⟩
    rw [← he] at hw
    obtain ⟨C,_,hc⟩ := hw
    linarith [C.spearmanFootrule_mem_Icc.1]

end Papers.Rockel2026XiFootrule
