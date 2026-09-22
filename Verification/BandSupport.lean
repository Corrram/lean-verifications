import Verification.BandSampling
import Verification.ScaledRampMean
import Mathlib.MeasureTheory.Measure.Support

/-! # Exact topological support of the sampled diagonal band -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- Closed-form lower edge of the support, as a convex function on the real line. -/
noncomputable def bandLowerEdge (b u : ℝ) : ℝ :=
  u-1/(2*b)+max 0 (1-b*u)^2/(2*b)

theorem bandLowerEdge_eq_mean {b : ℝ} (hb : 0 < b) (u : I) :
    bandLowerEdge b u = clampedMean b (b*(u : ℝ)) := by
  by_cases h : b*(u : ℝ) ≤ 1
  · rw [clampedMean_lower hb (mul_nonneg hb.le u.property.1)
      (by nlinarith [u.property.2]) h]
    unfold bandLowerEdge
    rw [max_eq_right (by linarith)]
    field_simp
    ring
  · rw [clampedMean_saturated hb (by linarith) (by nlinarith [u.property.2])]
    unfold bandLowerEdge
    rw [max_eq_left (by linarith)]
    field_simp
    ring

theorem bandUpperEdge_eq_mean {b : ℝ} (hb : 0 < b) (u : I) :
    1-bandLowerEdge b (1-(u : ℝ)) = clampedMean b (1+b*(u : ℝ)) := by
  have h := bandLowerEdge_eq_mean hb (unitInterval.symm u)
  change bandLowerEdge b (1-(u : ℝ)) = clampedMean b (b*(1-(u : ℝ))) at h
  rw [h, show 1+b*(u : ℝ) = b+1-b*(1-(u : ℝ)) by ring, clampedMean_complement]

noncomputable def bandSupport (b : ℝ) : Set (Fin 2 → ℝ) :=
  {x | (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ bandLowerEdge b (x 0) ≤ x 1 ∧
    x 1 ≤ 1-bandLowerEdge b (1-x 0)}

noncomputable def bandSampleReal (b : ℝ) (p : I × I) : Fin 2 → ℝ :=
  fun i => (bandSample b p i : ℝ)

@[fun_prop] theorem continuous_bandSampleReal (b : ℝ) : Continuous (bandSampleReal b) := by
  unfold bandSampleReal
  fun_prop

theorem range_bandSampleReal {b : ℝ} (hb : 0 < b) :
    Set.range (bandSampleReal b) = bandSupport b := by
  ext x
  constructor
  · rintro ⟨⟨u,z⟩,rfl⟩
    refine ⟨fun i => (bandSample b (u,z) i).property, ?_, ?_⟩
    · change bandLowerEdge b u ≤ clampedMean b (b*(u : ℝ)+(z : ℝ))
      rw [bandLowerEdge_eq_mean hb]
      exact clampedMean_monotone b (by linarith [z.property.1])
    · change clampedMean b (b*(u : ℝ)+(z : ℝ)) ≤ 1-bandLowerEdge b (1-(u : ℝ))
      rw [bandUpperEdge_eq_mean hb]
      exact clampedMean_monotone b (by linarith [z.property.2])
  · rintro ⟨hx,hl,hu⟩
    let u : I := ⟨x 0,hx 0⟩
    let v : I := ⟨x 1,hx 1⟩
    have hlow : clampedMean b (b*(u : ℝ)) ≤ (v : ℝ) := by
      rw [← bandLowerEdge_eq_mean hb]; exact hl
    have hupp : (v : ℝ) ≤ clampedMean b (1+b*(u : ℝ)) := by
      rw [← bandUpperEdge_eq_mean hb]; exact hu
    have ha := bandIntercept_mem b hb.le v
    have hbu : b*(u : ℝ) ∈ Icc (0 : ℝ) (b+1) :=
      ⟨mul_nonneg hb.le u.property.1, by nlinarith [u.property.2]⟩
    have hbu1 : 1+b*(u : ℝ) ∈ Icc (0 : ℝ) (b+1) :=
      ⟨by nlinarith [u.property.1], by nlinarith [u.property.2]⟩
    have h₁ : b*(u : ℝ) ≤ bandIntercept b hb.le v := (clampedMean_le_iff b hb.le hbu v).mp hlow
    have h₂ : bandIntercept b hb.le v ≤ 1+b*(u : ℝ) := by
      apply ((clampedMean_strictMonoOn hb.le).le_iff_le ha hbu1).mp
      rwa [bandIntercept_mean]
    let z : I := ⟨bandIntercept b hb.le v-b*(u : ℝ), by constructor <;> linarith⟩
    refine ⟨(u,z), ?_⟩
    ext i
    fin_cases i
    · rfl
    · change clampedMean b (b*(u : ℝ)+(bandIntercept b hb.le v-b*(u : ℝ))) = x 1
      rw [show b*(u : ℝ)+(bandIntercept b hb.le v-b*(u : ℝ)) = bandIntercept b hb.le v by ring,
        bandIntercept_mean]

theorem support_map_uniform (f : I × I → Fin 2 → ℝ) (hf : Continuous f) :
    ((volume : Measure (I × I)).map f).support = Set.range f := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed (isCompact_range hf).isClosed
    rw [mem_ae_iff, Measure.map_apply hf.measurable (isCompact_range hf).isClosed.isOpen_compl.measurableSet]
    have he : f ⁻¹' (Set.range f)ᶜ = ∅ := by ext p; simp
    rw [he, measure_empty]
  · rintro _ ⟨p,rfl⟩
    rw [Measure.support_eq_forall_isOpen]
    intro U hp hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    exact (hU.preimage hf).measure_pos volume ⟨p,hp⟩

/-- The topological support of the actual copula, embedded in the real square. -/
theorem diagonalBand_support_set {b : ℝ} (hb : 0 < b) :
    ((diagonalBand b hb.le).toMeasure.map (fun u i => (u i : ℝ))).support = bandSupport b := by
  rw [diagonalBand_toMeasure_sample, Measure.map_map (by fun_prop) (continuous_bandSample b).measurable]
  change ((volume : Measure (I × I)).map (bandSampleReal b)).support = _
  rw [support_map_uniform _ (continuous_bandSampleReal b), range_bandSampleReal hb]

end Verification
