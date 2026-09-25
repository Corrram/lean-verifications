import Verification.GaussianNormalDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open ProbabilityTheory MeasureTheory Set

namespace Verification

theorem standardNormalCDF_hasDerivAt (z : ℝ) :
    HasDerivAt (ProbabilityTheory.cdf (gaussianReal 0 1)) (gaussianPDFReal 0 1 z) z := by
  have hc : Continuous (gaussianPDFReal 0 1) := by unfold gaussianPDFReal; fun_prop
  have he : (ProbabilityTheory.cdf (gaussianReal 0 1) : ℝ→ℝ)=
      fun x => ProbabilityTheory.cdf (gaussianReal 0 1) 0+∫ t in (0:ℝ)..x,gaussianPDFReal 0 1 t := by
    funext x
    rw [gaussianReal_cdf_density 0 x (by norm_num : (1:NNReal)≠0),
      gaussianReal_cdf_density 0 0 (by norm_num : (1:NNReal)≠0),
      ← intervalIntegral.integral_Iic_sub_Iic
        (integrable_gaussianPDFReal 0 1).integrableOn (integrable_gaussianPDFReal 0 1).integrableOn]
    ring
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_add _

end Verification
