import Papers.AnsariRockel2026RhoFootrule.UpperLocalizedCurves
import Mathlib.Analysis.SpecificLimits.Basic
import Verification.CompactConvexHullPlane

/-! # Compactness of the localized upper seeds and their convex hull -/

open MeasureTheory ProbabilityTheory Verification Set Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2026RhoFootrule

private def upperSurface (p : ℝ × ℝ) : ℝ × ℝ :=
  (1-(1-2*p.2^2*(3-4*p.2))*p.1,1-(1-12*p.2^2*(1-p.2)^2)*p.1^2)

private theorem upperSurface_branch (n : ℕ) (a : ℝ) :
    upperSurface (1/((n : ℝ)+1),a) = upperBranch n a := by
  ext <;> simp [upperSurface,upperBranch,div_eq_mul_inv]

private theorem upperSeeds_image : upperSeeds =
    upperSurface '' (insert 0 (range (fun n : ℕ => 1/((n : ℝ)+1))) ×ˢ Icc (0 : ℝ) (1/2)) := by
  ext p
  constructor
  · intro hp
    rcases hp with he | hp
    · refine ⟨(0,0),⟨mem_insert _ _,by norm_num⟩,?_⟩
      simpa [upperSurface] using he.symm
    · obtain ⟨n,a,ha,rfl⟩ := mem_iUnion.mp hp
      exact ⟨(1/((n : ℝ)+1),a),⟨mem_insert_of_mem _ ⟨n,rfl⟩,ha⟩,upperSurface_branch n a⟩
  · rintro ⟨⟨q,a⟩,⟨hq,ha⟩,rfl⟩
    rcases hq with hq | ⟨n,rfl⟩
    · change q = 0 at hq
      subst q
      exact Or.inl (by simp [upperSurface])
    · exact Or.inr (mem_iUnion.mpr ⟨n,a,ha,upperSurface_branch n a |>.symm⟩)

/-- The countably many parameterized branches have just the included limit (1,1). -/
theorem upper_seeds_compact : IsCompact upperSeeds := by
  rw [upperSeeds_image]
  have hk : IsCompact (insert (0 : ℝ) (range (fun n : ℕ => 1/((n : ℝ)+1)))) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.isCompact_insert_range
  exact (hk.prod isCompact_Icc).image (by unfold upperSurface; fun_prop)

/-- Finite-dimensional compactness makes the upper convexified maximum attainable. -/
theorem upper_convex_hull_compact : IsCompact (convexHull ℝ upperSeeds) :=
  compact_convexHull_plane upper_seeds_compact

end Papers.AnsariRockel2026RhoFootrule
