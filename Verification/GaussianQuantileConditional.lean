import Verification.NormalQuantile

/-! # Gaussian conditional CDF on copula coordinates -/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def gaussianQuantileConditional (r : ℝ) (v u : I) : ℝ :=
  ProbabilityTheory.cdf (gaussianReal 0 1)
    ((normalQuantile v-r*normalQuantile u)/Real.sqrt (1-r^2))

theorem measurable_gaussianQuantileConditional (r : ℝ) (v : I) :
    Measurable (gaussianQuantileConditional r v) :=
  (monotone_cdf (gaussianReal 0 1)).measurable.comp
    ((measurable_const.sub (measurable_const.mul measurable_normalQuantile)).div_const _)

theorem gaussianBivariate_conditionalCDF_quantile {r : ℝ} (hr : r∈Ioo (-1) 1)
    {v : I} (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (fun u => (gaussianBivariate r ⟨hr.1.le,hr.2.le⟩).conditionalCDF u v)=ᵐ[volume]
      gaussianQuantileConditional r v := by
  let C := gaussianBivariate r ⟨hr.1.le,hr.2.le⟩
  have hm := map_cdfUnit (gaussianReal 0 1) continuous_standardNormalCDF
  have he : cdfUnit (gaussianReal 0 1) (normalQuantile v)=v :=
    Subtype.ext (cdf_normalQuantile hv)
  have hn := gaussianBivariate_conditionalCDF_normal hr (normalQuantile v)
  rw [he] at hn
  change (fun u => C.conditionalCDF u v)=ᵐ[volume] gaussianQuantileConditional r v
  rw [← hm]
  apply (ae_map_iff (measurable_cdfUnit _).aemeasurable
    (measurableSet_eq_fun (C.measurable_conditionalCDF_left v)
      (measurable_gaussianQuantileConditional r v))).2
  filter_upwards [hn] with x hx
  dsimp only [gaussianQuantileConditional]
  rw [normalQuantile_cdfUnit]
  exact hx

theorem gaussianQuantileConditional_antitoneOn {r : ℝ} (hr : 0≤r) (v : I) :
    AntitoneOn (gaussianQuantileConditional r v) {u : I | (u:ℝ)∈Ioo (0:ℝ) 1} := by
  intro u hu w hw huw
  apply (monotone_cdf (gaussianReal 0 1))
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hq := normalQuantile_strictMonoOn.monotoneOn hu hw huw
  have hp := mul_le_mul_of_nonneg_left hq hr
  linarith

theorem gaussianQuantileConditional_monotoneOn {r : ℝ} (hr : r≤0) (v : I) :
    MonotoneOn (gaussianQuantileConditional r v) {u : I | (u:ℝ)∈Ioo (0:ℝ) 1} := by
  intro u hu w hw huw
  apply (monotone_cdf (gaussianReal 0 1))
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  have hq := normalQuantile_strictMonoOn.monotoneOn hu hw huw
  have hp := mul_le_mul_of_nonpos_left hq hr
  linarith

end Verification
