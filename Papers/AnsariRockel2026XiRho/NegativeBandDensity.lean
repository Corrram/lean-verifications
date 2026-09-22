import Papers.AnsariRockel2026XiRho.BandDensityOpen
import Papers.AnsariRockel2026XiRho.BandSymmetry
import Verification.ReflectionDensity

/-! # The density of the negative branch -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- The exact reflected open-band density in Remark 3(c). -/
noncomputable def negativeSourceBandDensity (b : ℝ) (x : Fin 2 → I) : ℝ :=
  sourceBandDensityOpen b (Copula.reflectPoint {0} x)

theorem negativeSourceBand_toMeasure_density (b : ℝ) (hb : 0 < b) :
    (negativeSourceBand b hb).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (negativeSourceBandDensity b x)) := by
  change ((sourceBand b hb).reflect {0}).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
    (fun x => ENNReal.ofReal (sourceBandDensityOpen b (Copula.reflectPoint {0} x)))
  exact reflect_toMeasure_density (d := 2) (sourceBand b hb) {0}
    (f := fun x : Fin 2 → I => ENNReal.ofReal (sourceBandDensityOpen b x))
    (sourceBandDensityOpen_measurable hb).ennreal_ofReal (sourceBand_toMeasure_densityOpen b hb)

theorem negativeSourceBand_absolutelyContinuous (b : ℝ) (hb : 0 < b) :
    (negativeSourceBand b hb).toMeasure ≪ (volume : Measure (Fin 2 → I)) := by
  rw [negativeSourceBand_toMeasure_density]
  exact withDensity_absolutelyContinuous _ _

theorem negativeSourceBandDensity_formula (b : ℝ) (x : Fin 2 → I) :
    negativeSourceBandDensity b x =
      if b*(1-(x 0 : ℝ)) < sourceBandIntercept b (x 1) ∧
        sourceBandIntercept b (x 1) < b*(1-(x 0 : ℝ))+1 then sourceBandHeight b (x 1) else 0 := by
  simp [negativeSourceBandDensity, sourceBandDensityOpen, Copula.reflectPoint]

end Papers.AnsariRockel2026XiRho
