import Verification.StudentConditionalDensity
import Verification.ScaleMixtureAffine

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem studentConditionalDensity_cdf {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (x y : ℝ) :
    ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) y=
      ∫ t, ProbabilityTheory.cdf (gaussianReal 0 1)
        ((y-r*x)*Real.sqrt t/Real.sqrt (1-r^2))
          ∂gammaMeasure (ν/2+1/2) (ν/2+x^2/2) := by
  let μ := gammaProbability (ν/2+1/2) (ν/2+x^2/2) (by positivity) (by positivity)
  let s := fun t : ℝ => (Real.sqrt t)⁻¹*Real.sqrt (1-r^2)
  have hs : Measurable s := by fun_prop
  have hp : ∀ᵐ t ∂μ.toMeasure,0<s t := by
    filter_upwards [ae_pos_gammaMeasure (ν/2+1/2) (ν/2+x^2/2)] with t ht
    have hh : 0<1-r^2 := by nlinarith [hr.1,hr.2]
    dsimp only [s]
    positivity
  have he := normalScaleMixtureAffineLaw_withDensity μ s hs hp (r*x)
  change normalScaleMixtureAffineLaw μ s (r*x)=volume.withDensity (studentConditionalDensity r ν x) at he
  rw [← he,normalScaleMixtureAffineLaw_cdf μ s hs hp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only [s]
    rw [div_mul_eq_div_div,div_inv_eq_mul]

end Verification
