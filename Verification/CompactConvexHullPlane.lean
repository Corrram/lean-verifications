import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! # Compactness of convex hulls in the coefficient plane -/

open Set

namespace Verification

theorem compact_convexJoin_plane {S T : Set (ℝ × ℝ)} (hS : IsCompact S) (hT : IsCompact T) :
    IsCompact (convexJoin ℝ S T) := by
  let f := fun p : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) => (1-p.1) • p.2.1+p.1 • p.2.2
  have he : convexJoin ℝ S T = f '' (Icc (0 : ℝ) 1 ×ˢ (S ×ˢ T)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨x,hx,y,hy,hz⟩ := mem_convexJoin.mp hz
      rw [segment_eq_image] at hz
      obtain ⟨t,ht,rfl⟩ := hz
      exact ⟨(t,x,y),⟨ht,hx,hy⟩,rfl⟩
    · rintro ⟨⟨t,x,y⟩,⟨ht,hx,hy⟩,rfl⟩
      apply mem_convexJoin.mpr
      refine ⟨x,hx,y,hy,?_⟩
      rw [segment_eq_image]
      exact ⟨t,ht,rfl⟩
  rw [he]
  exact (isCompact_Icc.prod (hS.prod hT)).image (by dsimp [f]; fun_prop)

private theorem convexHull_plane_eq_triple (S : Set (ℝ × ℝ)) (hne : S.Nonempty) :
    convexHull ℝ S = convexJoin ℝ S (convexJoin ℝ S S) := by
  classical
  apply Subset.antisymm
  · intro z hz
    rw [convexHull_eq_union] at hz
    simp only [mem_iUnion] at hz
    obtain ⟨t,ht,hi,hz⟩ := hz
    have hc : t.card ≤ 3 := by
      have h := hi.card_le_finrank_succ
      have hv := Submodule.finrank_le (vectorSpan ℝ (range ((↑) : t → ℝ × ℝ)))
      have hd : Module.finrank ℝ (ℝ × ℝ) = 2 := by rw [Module.finrank_prod]; norm_num
      simp only [Fintype.card_coe] at h
      omega
    interval_cases hcard : t.card
    · have he : t = ∅ := Finset.card_eq_zero.mp hcard
      simp [he] at hz
    · obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hcard
      have hx : x ∈ S := ht (by simp)
      have he : z=x := by simpa using hz
      subst z
      exact subset_convexJoin_left ⟨x,segment_subset_convexJoin hx hx (left_mem_segment ℝ x x)⟩ hx
    · obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hcard
      have hx : x ∈ S := ht (by simp)
      have hy : y ∈ S := ht (by simp)
      have hz' : z ∈ segment ℝ x y := by simpa [convexHull_pair] using hz
      exact subset_convexJoin_right hne (segment_subset_convexJoin hx hy hz')
    · obtain ⟨x,y,w,hxy,hxw,hyw,rfl⟩ := Finset.card_eq_three.mp hcard
      have hx : x ∈ S := ht (by simp)
      have hy : y ∈ S := ht (by simp)
      have hw : w ∈ S := ht (by simp)
      have hz' : z ∈ convexJoin ℝ {x} (segment ℝ y w) := by
        rw [convexJoin_singleton_segment]
        simpa using hz
      exact convexJoin_mono (singleton_subset_iff.mpr hx) (segment_subset_convexJoin hy hw) hz'
  · exact convexJoin_subset (subset_convexHull ℝ S)
      (convexJoin_subset (subset_convexHull ℝ S) (subset_convexHull ℝ S) (convex_convexHull ℝ S))
      (convex_convexHull ℝ S)

/-- Caratheodory reduces the hull to joins of three points, a compact image. -/
theorem compact_convexHull_plane {S : Set (ℝ × ℝ)} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  rw [convexHull_plane_eq_triple S hne]
  exact compact_convexJoin_plane hS (compact_convexJoin_plane hS hS)

end Verification
