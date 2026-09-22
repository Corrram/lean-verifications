import Papers.AnsariRockel2026RhoFootrule.UpperBinaryCurve
import Papers.AnsariRockel2026RhoFootrule.InnerConvexity
import Verification.EqualBlocksDirectional

/-! # Every localized upper inner branch -/

open MeasureTheory ProbabilityTheory Verification Set
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

/-- The source branch number is n+1, so there is no zero-block convention. -/
noncomputable def upperLocalized (n : ℕ) (a : I) : Copula 2 := equalBlocks n (upperBinary a)

noncomputable def upperBranch (n : ℕ) (a : ℝ) : ℝ × ℝ :=
  (1-(1-2*a^2*(3-4*a))/((n : ℝ)+1),1-(1-12*a^2*(1-a)^2)/((n : ℝ)+1)^2)

/-- The localization identities used to derive equation (120), including degenerate blocks. -/
theorem ordinal_directional_coefficients (C D : Copula 2) (a : I) :
    (C.ordinalSum D a).chatterjeeXi =
      1-(a : ℝ)^2*(1-C.chatterjeeXi)-(1-(a : ℝ))^2*(1-D.chatterjeeXi) ∧
    copulaCorrelationRatio (C.ordinalSum D a) =
      1-(a : ℝ)^3*(1-copulaCorrelationRatio C)-(1-(a : ℝ))^3*(1-copulaCorrelationRatio D) :=
  ⟨chatterjeeXi_ordinalSum C D a,correlationRatio_ordinalSum C D a⟩

/-- Equal localization into n+1 blocks for an arbitrary base copula. -/
theorem equal_block_directional_coefficients (n : ℕ) (C : Copula 2) :
    (equalBlocks n C).chatterjeeXi=1-(1-C.chatterjeeXi)/((n : ℝ)+1) ∧
    copulaCorrelationRatio (equalBlocks n C)=1-(1-copulaCorrelationRatio C)/((n : ℝ)+1)^2 :=
  ⟨equalBlocks_xi n C,equalBlocks_correlationRatio n C⟩

/-- Equation (120), with every positive block count represented. -/
theorem upperLocalized_coefficients (n : ℕ) (a : I) (ha : (a : ℝ) ≤ 1/2) :
    (upperLocalized n a).chatterjeeXi = (upperBranch n a).1 ∧
      copulaCorrelationRatio (upperLocalized n a) = (upperBranch n a).2 := by
  constructor
  · rw [upperLocalized,equalBlocks_xi,(upperBinary_coefficients a ha).1]
    rfl
  · change correlationRatio (equalBlocks n (upperBinary a)) = _
    have h : correlationRatio (upperBinary a) = 12*(a : ℝ)^2*(1-(a : ℝ))^2 := (upperBinary_coefficients a ha).2
    rw [equalBlocks_correlationRatio,h]
    rfl

/-- All upper branches are actual copula coefficient pairs. -/
theorem upper_branch_attained (n : ℕ) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) (1/2)) :
    upperBranch n a ∈ directionalRegion := by
  let t : I := ⟨a,ha.1,by linarith [ha.2]⟩
  exact ⟨upperLocalized n t,upperLocalized_coefficients n t ha.2⟩

/-- The comonotonic limit point is also attained. -/
theorem upper_limit_attained : (1,1) ∈ directionalRegion := by
  have he := partialReveal_coefficients (1 : I)
  refine ⟨partialReveal 1,?_,?_⟩ <;> norm_num at he ⊢ <;> tauto

/-- Continuous dependence of every finite branch on its binary parameter. -/
theorem upper_branch_continuous (n : ℕ) : Continuous (upperBranch n) := by
  unfold upperBranch
  fun_prop

/-- The source set in equation (45). -/
def upperSeeds : Set (ℝ × ℝ) :=
  insert (1,1) (⋃ n : ℕ, upperBranch n '' Icc (0 : ℝ) (1/2))

theorem upper_seeds_attained : upperSeeds ⊆ directionalRegion := by
  intro p hp
  rcases hp with he | hp
  · simpa only [he] using upper_limit_attained
  · obtain ⟨n,a,ha,rfl⟩ := mem_iUnion.mp hp
    exact upper_branch_attained n a ha

theorem upper_convex_hull_attained : convexHull ℝ upperSeeds ⊆ directionalRegion :=
  convex_hull_attained upperSeeds upper_seeds_attained

end Papers.AnsariRockel2026RhoFootrule
