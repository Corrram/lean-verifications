import Verification.GammaPrecisionMoments

open ProbabilityTheory MeasureTheory Real Set Filter
open scoped ENNReal Topology

namespace Verification

theorem gammaPrecision_concentration_bound {a ε : ℝ} (ha : 0<a) (hε : 0<ε) :
    (gammaMeasure a a).real {t | ε≤|t-1|}≤a⁻¹/ε^2 := by
  obtain ⟨hi,he⟩ := gammaPrecision_centered_second_moment ha
  have h := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun t : ℝ => sq_nonneg (t-1))) hi (ε^2)
  rw [he] at h
  have hs : {t : ℝ | ε^2≤(t-1)^2}={t : ℝ | ε≤|t-1|} := by
    ext t
    change (ε^2≤(t-1)^2) ↔ ε≤|t-1|
    rw [← sq_abs (t-1),sq_le_sq₀ hε.le (abs_nonneg _)]
  rw [hs] at h
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa only [mul_comm] using h)

theorem gammaPrecision_concentrates {ι : Type*} {l : Filter ι}
    (a : ι→ℝ) (ha : ∀ i,0<a i) (ht : Tendsto a l atTop)
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun i => (gammaMeasure (a i) (a i)).real {t | ε≤|t-1|}) l (nhds 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun i => gammaPrecision_concentration_bound (ha i) hε)
  simpa only [zero_div,Function.comp_apply] using (tendsto_inv_atTop_zero.comp ht).div_const (ε^2)

end Verification
