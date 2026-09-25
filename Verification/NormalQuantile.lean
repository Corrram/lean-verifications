import Verification.GaussianConditional

/-! # The standard normal quantile on the open unit interval -/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem measurableEmbedding_standardNormalCDF :
    MeasurableEmbedding (ProbabilityTheory.cdf (gaussianReal 0 1)) :=
  continuous_standardNormalCDF.measurableEmbedding standardNormalCDF_strictMono.injective

noncomputable def normalQuantile (u : I) : ℝ :=
  measurableEmbedding_standardNormalCDF.invFun (u:ℝ)

theorem measurable_normalQuantile : Measurable normalQuantile :=
  measurableEmbedding_standardNormalCDF.measurable_invFun.comp measurable_subtype_coe

theorem normalCDF_mem_Ioo (x : ℝ) :
    ProbabilityTheory.cdf (gaussianReal 0 1) x∈Ioo (0:ℝ) 1 := by
  constructor
  · have h := standardNormalCDF_strictMono (show x-1<x by linarith)
    have hn := cdf_nonneg (gaussianReal 0 1) (x-1)
    linarith
  · have h := standardNormalCDF_strictMono (show x<x+1 by linarith)
    have hn := cdf_le_one (gaussianReal 0 1) (x+1)
    linarith

theorem normalQuantile_cdfUnit (x : ℝ) : normalQuantile (cdfUnit (gaussianReal 0 1) x)=x :=
  measurableEmbedding_standardNormalCDF.leftInverse_invFun x

theorem cdf_normalQuantile {u : I} (hu : (u:ℝ)∈Ioo (0:ℝ) 1) :
    ProbabilityTheory.cdf (gaussianReal 0 1) (normalQuantile u)=(u:ℝ) := by
  obtain ⟨x,hx⟩ := exists_cdf_eq_of_continuous (gaussianReal 0 1)
    continuous_standardNormalCDF hu.1 hu.2
  have he : cdfUnit (gaussianReal 0 1) x=u := Subtype.ext hx
  rw [← he,normalQuantile_cdfUnit]
  rfl

theorem normalQuantile_strictMonoOn :
    StrictMonoOn normalQuantile {u : I | (u:ℝ)∈Ioo (0:ℝ) 1} := by
  intro u hu v hv huv
  apply standardNormalCDF_strictMono.lt_iff_lt.mp
  rw [cdf_normalQuantile hu,cdf_normalQuantile hv]
  exact huv

end Verification
