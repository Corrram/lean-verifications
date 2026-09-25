import Verification.QuadrantIntegral

open MeasureTheory Set
open scoped ENNReal

namespace Verification

theorem lintegral_mul_Ioi (f : ℝ → ℝ≥0∞) {x : ℝ} (hx : 0<x) :
    (∫⁻ y in Ioi (0:ℝ), f y)=
      ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal x*f (x*s) := by
  have hi : (fun s : ℝ => x*s) '' Ioi 0=Ioi 0 := by
    ext y
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact mul_pos hx hs
    · intro hy
      exact ⟨y/x,div_pos hy hx,mul_div_cancel₀ y hx.ne'⟩
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun s (_ : s∈Ioi (0:ℝ)) => ((hasDerivAt_id s).const_mul x).hasDerivWithinAt)
    (show InjOn (fun s : ℝ => x*s) (Ioi 0) from
      fun _ _ _ _ h => mul_left_cancel₀ hx.ne' h) f
  simpa only [id_eq,mul_one,hi,abs_of_pos hx] using hh

theorem lintegral_quadrant_scale (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in Ioi (0:ℝ), ∫⁻ y in Ioi (0:ℝ), f (x,y))=
      ∫⁻ s in Ioi (0:ℝ), ∫⁻ x in Ioi (0:ℝ), ENNReal.ofReal x*f (x,x*s) := by
  have he : (∫⁻ x in Ioi (0:ℝ), ∫⁻ y in Ioi (0:ℝ), f (x,y))=
      ∫⁻ x in Ioi (0:ℝ), ∫⁻ s in Ioi (0:ℝ), ENNReal.ofReal x*f (x,x*s) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact lintegral_mul_Ioi _ hx
  rw [he,lintegral_lintegral_swap]
  exact ((measurable_fst.ennreal_ofReal).mul
    (hf.comp (measurable_fst.prodMk (measurable_fst.mul measurable_snd)))).aemeasurable

theorem integral_quadrant_scale (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hn : ∀ z, 0≤f z)
    (hi : Integrable f ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0)))) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), f (x,y))=
      ∫ s in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ), max 0 x*f (x,x*s) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let g : ℝ × ℝ → ℝ := fun z => max 0 z.2*f (z.2,z.2*z.1)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have hgn (z : ℝ × ℝ) : 0≤g z := mul_nonneg (le_max_left _ _) (hn _)
  have he : (∫⁻ z, ENNReal.ofReal (g z) ∂μ.prod μ)=
      ∫⁻ z, ENNReal.ofReal (f z) ∂μ.prod μ := by
    rw [lintegral_prod _ hg.ennreal_ofReal.aemeasurable,
      lintegral_prod _ hf.ennreal_ofReal.aemeasurable,lintegral_quadrant_scale _ hf.ennreal_ofReal]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro s _
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp [g]
    rw [max_eq_right (le_of_lt hx),ENNReal.ofReal_mul (le_of_lt hx)]
  have hgi : Integrable g (μ.prod μ) := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hgn),he]
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)).mp hi.2
  rw [← integral_prod _ hi,← integral_prod _ hgi]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hi.1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgn) hgi.1,he]

end Verification
