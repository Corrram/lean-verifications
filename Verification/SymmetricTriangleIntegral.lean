import Verification.KendallConditionalProduct

/-! # Integration of symmetric functions over the two triangles of the unit square -/

open MeasureTheory Set Filter
open scoped unitInterval

namespace Verification

theorem integral_symmetric_triangle_of_integrable (f : I × I → ℝ) (hi : Integrable f)
    (hs : ∀ p, f p.swap=f p) :
    (∫ u : I,∫ v : I,f (u,v))=2*(∫ u : I,∫ v in Iic u,f (u,v)) := by
  classical
  let L : I × I → ℝ := {p : I × I | p.2≤p.1}.indicator f
  have hL : Integrable L := hi.indicator (measurableSet_le measurable_snd measurable_fst)
  have hLs : Integrable (fun p : I × I => L p.swap) := hL.swap
  have hne : ∀ᵐ p : I × I,p.2≠p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun measurable_snd measurable_fst).compl).mpr
    exact Eventually.of_forall fun u => Measure.ae_ne volume u
  have he : f =ᵐ[volume] fun p => L p+L p.swap := by
    filter_upwards [hne] with p hp
    rcases lt_or_gt_of_ne hp with h | h
    · simp only [L,indicator_of_mem (show p∈{p : I × I | p.2≤p.1} from h.le),
        indicator_of_notMem (show p.swap∉{p : I × I | p.2≤p.1} from not_le.mpr h),add_zero]
    · simp only [L,indicator_of_notMem (show p∉{p : I × I | p.2≤p.1} from not_le.mpr h),
        indicator_of_mem (show p.swap∈{p : I × I | p.2≤p.1} from h.le),zero_add,hs]
  rw [← integral_prod _ hi]
  change (∫ p : I × I,f p)=_
  rw [integral_congr_ae he,integral_add (g := fun p : I × I => L p.swap) hL hLs]
  have hswap : (∫ p : I × I,L p.swap)=(∫ p : I × I,L p) := integral_prod_swap L
  rw [hswap]
  have hleft : (∫ p : I × I,L p)=(∫ u : I,∫ v in Iic u,f (u,v)) := by
    rw [Measure.volume_eq_prod,integral_prod _ hL]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      change (∫ v : I,L (u,v))=(∫ v in Iic u,f (u,v))
      rw [← integral_indicator measurableSet_Iic]
      rfl
  rw [hleft]
  ring

theorem integral_symmetric_triangle (f : I × I → ℝ) (hf : Measurable f)
    (hb : ∀ p, f p ∈ Icc (0:ℝ) 1) (hs : ∀ p, f p.swap=f p) :
    (∫ u : I,∫ v : I,f (u,v))=2*(∫ u : I,∫ v in Iic u,f (u,v)) := by
  apply integral_symmetric_triangle_of_integrable f _ hs
  exact (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hb p).1] using (hb p).2)

end Verification
