import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped ENNReal

namespace Verification

theorem lintegral_add_Ioi (f : ℝ → ℝ≥0∞) (x : ℝ) :
    (∫⁻ y in Ioi (0:ℝ), f (x+y))=∫⁻ t in Ioi x, f t := by
  have hi : (fun y : ℝ => x+y) '' Ioi 0=Ioi x := by
    ext t
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa using hy
    · intro ht
      exact ⟨t-x,by change 0<t-x; change x<t at ht; linarith,by ring⟩
  have hh := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun y (_ : y∈Ioi (0:ℝ)) => ((hasDerivAt_id y).const_add x).hasDerivWithinAt)
    (show InjOn (fun y : ℝ => x+y) (Ioi 0) from fun _ _ _ _ h => add_left_cancel h) f
  simpa only [id_eq,hi,abs_one,ENNReal.ofReal_one,one_mul] using hh.symm

theorem lintegral_quadrant_sum (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in Ioi (0:ℝ), ∫⁻ y in Ioi (0:ℝ), f (x+y))=
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal t*f t := by
  simp_rw [lintegral_add_Ioi,← lintegral_indicator measurableSet_Ioi]
  have ho (x : ℝ) : (Ioi (0:ℝ)).indicator
      (fun x => ∫⁻ t, (Ioi x).indicator f t) x =
      ∫⁻ t, (Ioi (0:ℝ)).indicator (fun x => (Ioi x).indicator f t) x := by
    by_cases hx : x∈Ioi (0:ℝ) <;> simp [hx]
  simp_rw [ho]
  rw [lintegral_lintegral_swap]
  · apply lintegral_congr
    intro t
    by_cases ht : 0<t
    · have he : (fun x : ℝ => (Ioi (0:ℝ)).indicator
          (fun x => (Ioi x).indicator f t) x) = (Ioo 0 t).indicator (fun _ => f t) := by
        funext x
        simp only [indicator,mem_Ioi,mem_Ioo]
        split_ifs <;> simp_all
      rw [he,lintegral_indicator measurableSet_Ioo,lintegral_const]
      simp [ht,Real.volume_Ioo,mul_comm]
    · have he : (fun x : ℝ => (Ioi (0:ℝ)).indicator
          (fun x => (Ioi x).indicator f t) x)=0 := by
        funext x
        simp only [indicator,mem_Ioi,Pi.zero_apply]
        split_ifs <;> simp_all
        linarith
      rw [he]
      simp only [indicator_of_notMem (show t∉Ioi (0:ℝ) from ht)]
      change (∫⁻ _ : ℝ, (0:ℝ≥0∞))=0
      exact lintegral_zero
  · exact (((hf.comp measurable_snd).indicator
      (measurableSet_lt measurable_fst measurable_snd)).indicator
      (measurableSet_Ioi.preimage measurable_fst)).aemeasurable

theorem integral_quadrant_sum (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ t, 0≤f t)
    (hi : IntegrableOn (fun t => t*f t) (Ioi (0:ℝ))) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), f (x+y))=
      ∫ t in Ioi (0:ℝ), t*f t := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  have hm : Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (f (z.1+z.2))) := by
    fun_prop
  have hn' : 0 ≤ᵐ[μ] (fun t => t*f t) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact mul_nonneg (le_of_lt ht) (hn t)
  have he : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f (x+y)) ∂μ ∂μ)=
      ENNReal.ofReal (∫ t in Ioi (0:ℝ), t*f t) := by
    rw [lintegral_quadrant_sum _ hf.ennreal_ofReal]
    rw [ofReal_integral_eq_lintegral_ofReal hi hn']
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    exact (ENNReal.ofReal_mul (le_of_lt ht)).symm
  have hq : Integrable (fun z : ℝ × ℝ => f (z.1+z.2)) (μ.prod μ) := by
    refine ⟨(hf.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => hn _)]
    rw [lintegral_prod _ hm.aemeasurable,he]
    exact ENNReal.ofReal_lt_top
  rw [← integral_prod _ hq]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hn _) hq.1]
  rw [lintegral_prod _ hm.aemeasurable,he]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae hn')

end Verification
