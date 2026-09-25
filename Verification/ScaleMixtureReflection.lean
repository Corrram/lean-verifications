import Verification.ScaleMixtureCDF
import Verification.StudentBivariate

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussianScaleMixture_toMeasure {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).toMeasure=
      ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).prod μ.toMeasure).map
        (fun p i => cdfUnit (normalScaleMixtureMarginal μ s) (s p.2*p.1 i)) := by
  change ((gaussianScaleMixtureLaw (bivariateCorrelation r) μ s).toMeasure).map
    (marginalTransform (gaussianScaleMixtureLaw (bivariateCorrelation r) μ s))=_
  change (((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).prod μ.toMeasure).map
    (fun p i => s p.2*p.1 i)).map _=_
  rw [Measure.map_map (measurable_marginalTransform _) (by fun_prop)]
  congr 1
  funext p i
  dsimp only [Function.comp_def,marginalTransform]
  rw [gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) μ s hs i]
  rfl

theorem normalScaleMixtureMarginal_cdfUnit_neg (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ)
    (hs : Measurable s) (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) (x : ℝ) :
    cdfUnit (normalScaleMixtureMarginal μ s) (-x)=
      unitInterval.symm (cdfUnit (normalScaleMixtureMarginal μ s) x) := by
  apply Subtype.ext
  exact normalScaleMixtureMarginal_cdf_neg μ s hs hp x

theorem gaussianScaleMixture_neg {r : ℝ} (hr : r∈Icc (-1) 1)
    (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    gaussianScaleMixture (bivariateCorrelation (-r))
      (bivariateCorrelation_posSemidef (by constructor <;> linarith [hr.1,hr.2]))
      (by intro i; fin_cases i <;> rfl) μ s hs hp=
    (gaussianScaleMixture (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
      (by intro i; fin_cases i <;> rfl) μ s hs hp).reflect {1} := by
  have hn : -r∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2]
  let G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let F := fun p : EuclideanSpace ℝ (Fin 2)×ℝ => fun i =>
    cdfUnit (normalScaleMixtureMarginal μ s) (s p.2*p.1 i)
  have hF : Measurable F := by fun_prop
  apply Copula.ext
  rw [toMeasure_reflect,gaussianScaleMixture_toMeasure hn μ s hs hp,
    gaussianScaleMixture_toMeasure hr μ s hs hp,← map_gaussianNegSecond hr]
  change ((G.map gaussianNegSecond).prod μ.toMeasure).map F=
    ((G.prod μ.toMeasure).map F).map (reflectPoint {1})
  have hm : (G.map gaussianNegSecond).prod μ.toMeasure=
      (G.prod μ.toMeasure).map (Prod.map gaussianNegSecond id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map G μ.toMeasure
      gaussianNegSecond.measurable measurable_id
  rw [hm,Measure.map_map hF (by fun_prop),Measure.map_map (measurable_reflectPoint _) hF]
  congr 1
  funext p i
  fin_cases i <;> simp [F,gaussianNegSecond_apply,reflectPoint,
    normalScaleMixtureMarginal_cdfUnit_neg μ s hs hp]

theorem studentBivariate_neg {r : ℝ} (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    studentBivariate (-r) (by constructor <;> linarith [hr.1,hr.2]) ν hν=
      (studentBivariate r hr ν hν).reflect {1} :=
  gaussianScaleMixture_neg hr
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

end Verification
