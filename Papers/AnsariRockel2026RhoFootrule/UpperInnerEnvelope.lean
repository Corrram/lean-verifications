import Papers.AnsariRockel2026RhoFootrule.UpperSeedsProjection
import Mathlib.Analysis.Convex.Function

/-! # The attained concave upper envelope and the complete inner enclosure -/

open MeasureTheory ProbabilityTheory Verification Set
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

/-- The exact supremum in equation (45); attainment is proved below. -/
noncomputable def upperInnerRatio (x : ℝ) : ℝ :=
  sSup {y : ℝ | (x,y) ∈ convexHull ℝ upperSeeds}

private theorem upper_slice_has_max (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ y, IsGreatest {y : ℝ | (x,y) ∈ convexHull ℝ upperSeeds} y := by
  let K := convexHull ℝ upperSeeds ∩ {p : ℝ × ℝ | p.1=x}
  have hk : IsCompact K := upper_convex_hull_compact.inter_right (isClosed_eq continuous_fst continuous_const)
  obtain ⟨y,hy⟩ := upper_seed_at_each_x x hx
  have hne : K.Nonempty := ⟨(x,y),subset_convexHull ℝ upperSeeds hy,rfl⟩
  obtain ⟨p,hp,hm⟩ := hk.exists_isMaxOn hne continuous_snd.continuousOn
  rcases p with ⟨u,y⟩
  rcases hp with ⟨hp,he⟩
  change u=x at he
  subst u
  refine ⟨y,hp,?_⟩
  intro z hz
  exact hm ⟨hz,rfl⟩

/-- The maximum defining the source upper inner boundary exists at every x. -/
theorem upperInnerRatio_isGreatest (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    IsGreatest {y : ℝ | (x,y) ∈ convexHull ℝ upperSeeds} (upperInnerRatio x) := by
  obtain ⟨y,hy⟩ := upper_slice_has_max x hx
  rwa [upperInnerRatio,hy.csSup_eq]

/-- The upper ordinate is attained by a genuine copula. -/
theorem upper_inner_attained (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ C : Copula 2, C.chatterjeeXi=x ∧ copulaCorrelationRatio C=upperInnerRatio x :=
  upper_convex_hull_attained (upperInnerRatio_isGreatest x hx).1

theorem upperInnerRatio_mem (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : upperInnerRatio x ∈ Icc (0 : ℝ) 1 :=
  (directional_region_bounds (upper_convex_hull_attained (upperInnerRatio_isGreatest x hx).1)).2

/-- Concavity of the upper boundary follows from its attained convex-hull maxima. -/
theorem upper_inner_concave : ConcaveOn ℝ (Icc (0 : ℝ) 1) upperInnerRatio := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hm := convex_convexHull ℝ upperSeeds (upperInnerRatio_isGreatest x hx).1
    (upperInnerRatio_isGreatest y hy).1 ha hb hab
  have hxy := convex_Icc (0 : ℝ) 1 hx hy ha hb hab
  exact (upperInnerRatio_isGreatest (a • x+b • y) hxy).2 hm

private theorem diagonal_in_upper_hull (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    (x,x) ∈ convexHull ℝ upperSeeds := by
  have h0 : (0,0) ∈ upperSeeds := by
    refine Or.inr (mem_iUnion.mpr ⟨0,0,by norm_num,?_⟩)
    norm_num [upperBranch]
  have h1 : (1,1) ∈ upperSeeds := Or.inl rfl
  have h := convex_convexHull ℝ upperSeeds (subset_convexHull ℝ upperSeeds h1)
    (subset_convexHull ℝ upperSeeds h0) hx.1 (sub_nonneg.mpr hx.2) (show x+(1-x)=1 by ring)
  simpa using h

/-- The envelope is at least the diagonal, since its seed set contains (0,0) and (1,1). -/
theorem le_upperInnerRatio (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : x ≤ upperInnerRatio x :=
  (upperInnerRatio_isGreatest x hx).2 (diagonal_in_upper_hull x hx)

theorem lowerInnerRatio_le_self (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : lowerInnerRatio x ≤ x := by
  by_cases h : x ≤ 1/4
  · simpa only [lowerInnerRatio,ite_eq_left h] using hx.1
  have hz : 0 ≤ (4*x-1)/3 := by linarith
  have hs := Real.sq_sqrt hz
  have hn := Real.sqrt_nonneg ((4*x-1)/3)
  have h1 : Real.sqrt ((4*x-1)/3) ≤ 1 := by nlinarith [hx.2]
  rw [lowerInnerRatio,ite_eq_right h]
  nlinarith [mul_nonneg (sq_nonneg (Real.sqrt ((4*x-1)/3))) (sub_nonneg.mpr h1)]

/-- The two attained constructions are ordered at every horizontal coordinate. -/
theorem inner_curve_order (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : lowerInnerRatio x ≤ upperInnerRatio x :=
  (lowerInnerRatio_le_self x hx).trans (le_upperInnerRatio x hx)

/-- Proposition 2.10, equation (46): every point of the entire inner enclosure is attained. -/
theorem full_inner_enclosure (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (lowerInnerRatio x) (upperInnerRatio x)) :
    ∃ C : Copula 2, C.chatterjeeXi=x ∧ copulaCorrelationRatio C=y :=
  directional_vertical_interval x _ _ y (lower_inner_attained x hx) (upper_inner_attained x hx) hy

end Papers.AnsariRockel2026RhoFootrule
