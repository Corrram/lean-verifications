import Verification.StudentConditionalDensity
import Verification.ScaleMixtureAffine
import Verification.GammaScaling

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

theorem studentConditionalDensity_cdf_standard {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (x y : ℝ) :
    ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) y=
      ProbabilityTheory.cdf (normalScaleMixtureMarginal
        (gammaProbability ((ν+1)/2) ((ν+1)/2) (by positivity) (by positivity))
        (fun t => (Real.sqrt t)⁻¹))
        ((y-r*x)/Real.sqrt ((ν+x^2)*(1-r^2)/(ν+1))) := by
  let a := (ν+1)/2
  let b := ν/2+x^2/2
  let c := b/a
  have ha : 0<a := by dsimp [a]; positivity
  have hb : 0<b := by dsimp [b]; positivity
  have hc : 0<c := div_pos hb ha
  have hd : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  have hrate : b/c=a := by dsimp [c]; field_simp
  have hmap : (gammaMeasure a b).map (fun t => c*t)=gammaMeasure a a := by
    rw [gammaMeasure_map_mul hb hc,hrate]
  have hscale : (ν+x^2)*(1-r^2)/(ν+1)=c*(1-r^2) := by
    dsimp [c,b,a]
    field_simp
  rw [studentConditionalDensity_cdf hr ν hν x y,
    normalScaleMixtureMarginal_cdf _ _ (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure a a] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))]
  simp only [div_inv_eq_mul]
  rw [show ν/2+1/2=(ν+1)/2 by ring]
  change (∫ t, ProbabilityTheory.cdf (gaussianReal 0 1)
      ((y-r*x)*Real.sqrt t/Real.sqrt (1-r^2)) ∂gammaMeasure a b)=
    ∫ t, ProbabilityTheory.cdf (gaussianReal 0 1)
      ((y-r*x)/Real.sqrt ((ν+x^2)*(1-r^2)/(ν+1))*Real.sqrt t) ∂gammaMeasure a a
  have hm : Measurable (fun t : ℝ => ProbabilityTheory.cdf (gaussianReal 0 1)
      ((y-r*x)/Real.sqrt ((ν+x^2)*(1-r^2)/(ν+1))*Real.sqrt t)) :=
    (monotone_cdf (gaussianReal 0 1)).measurable.comp (by fun_prop)
  rw [← hmap,integral_map (by fun_prop) hm.aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [hscale,Real.sqrt_mul hc.le,Real.sqrt_mul hc.le]
    congr 1
    have hsc := (Real.sqrt_pos.mpr hc).ne'
    have hsd := (Real.sqrt_pos.mpr hd).ne'
    field_simp

end Verification
