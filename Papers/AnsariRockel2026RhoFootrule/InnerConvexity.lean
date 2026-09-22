import Papers.AnsariRockel2026RhoFootrule.LowerInnerCurve
import Verification.ConditionalJoinRank
import Mathlib.Analysis.Convex.Hull

/-! # Convexity of the directional xi--eta attainable region -/

open MeasureTheory ProbabilityTheory Verification Set
open scoped unitInterval

namespace Papers.AnsariRockel2026RhoFootrule

/-- Actual copula coefficient pairs, with the predictor in the first coordinate. -/
def directionalRegion : Set (ℝ × ℝ) :=
  {p | ∃ C : Copula 2, C.chatterjeeXi = p.1 ∧ copulaCorrelationRatio C = p.2}

/-- Equations (117)--(118): the tagged construction realizes both affine coordinates. -/
theorem tagged_coefficients (C D : Copula 2) (a : I) (ha0 : 0 < a) (ha1 : a < 1) :
    (conditionalJoin C D a ha0 ha1).chatterjeeXi = (a : ℝ)*C.chatterjeeXi+(1-(a : ℝ))*D.chatterjeeXi ∧
    copulaCorrelationRatio (conditionalJoin C D a ha0 ha1) =
      (a : ℝ)*copulaCorrelationRatio C+(1-(a : ℝ))*copulaCorrelationRatio D :=
  ⟨conditionalJoin_xi C D a ha0 ha1,conditionalJoin_correlationRatio C D a ha0 ha1⟩

/-- Proposition 2.10: every convex combination of attained pairs is attained. -/
theorem directional_region_convex : Convex ℝ directionalRegion := by
  rintro p ⟨C,hCx,hCy⟩ q ⟨D,hDx,hDy⟩ a b ha hb hab
  change ∃ E : Copula 2, E.chatterjeeXi = a*p.1+b*q.1 ∧ copulaCorrelationRatio E = a*p.2+b*q.2
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    exact ⟨D,by simpa [ha0,hb1] using hDx,by simpa [ha0,hb1] using hDy⟩
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    exact ⟨C,by simpa [ha1,hb0] using hCx,by simpa [ha1,hb0] using hCy⟩
  let t : I := ⟨a,ha,by linarith⟩
  have ht0 : 0 < t := by change 0 < a; exact lt_of_le_of_ne ha (Ne.symm ha0)
  have ht1 : t < 1 := by change a < 1; linarith [lt_of_le_of_ne hb (Ne.symm hb0)]
  have ht : 1-a=b := by linarith
  refine ⟨conditionalJoin C D t ht0 ht1,?_,?_⟩
  · simpa only [t,hCx,hDx,ht] using (tagged_coefficients C D t ht0 ht1).1
  · simpa only [t,hCy,hDy,ht] using (tagged_coefficients C D t ht0 ht1).2

/-- Convexification of any collection of actual witnesses preserves attainability. -/
theorem convex_hull_attained (S : Set (ℝ × ℝ)) (hS : S ⊆ directionalRegion) :
    convexHull ℝ S ⊆ directionalRegion :=
  convexHull_min hS directional_region_convex

/-- An attained lower and upper ordinate fill the entire vertical interval. -/
theorem directional_vertical_interval (x l u y : ℝ)
    (hl : (x,l) ∈ directionalRegion) (hu : (x,u) ∈ directionalRegion)
    (hy : y ∈ Icc l u) : (x,y) ∈ directionalRegion := by
  by_cases he : l = u
  · have hy' : y = l := by rw [← he] at hy; exact le_antisymm hy.2 hy.1
    simpa [hy'] using hl
  have hp : 0 < u-l := sub_pos.mpr (lt_of_le_of_ne (hy.1.trans hy.2) he)
  let a := (u-y)/(u-l)
  let b := (y-l)/(u-l)
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hy.2) hp.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hy.1) hp.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have h := directional_region_convex hl hu ha hb hab
  have heq : a • (x,l)+b • (x,u) = (x,y) := by
    ext <;> dsimp [a,b] <;> field_simp <;> ring
  rwa [heq] at h

end Papers.AnsariRockel2026RhoFootrule
