import Verification.GaussianReflection

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def gaussianMix (r : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (![EuclideanSpace.proj 0,
      r • EuclideanSpace.proj 0+Real.sqrt (1-r^2) • EuclideanSpace.proj 1]))

noncomputable def gaussianMixRow (r : ℝ) (i : Fin 2) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (!![1,0;r,Real.sqrt (1-r^2)] i)

theorem gaussianMix_inner (r : ℝ) (i : Fin 2) :
    (fun u => inner (𝕜 := ℝ) ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) u) ∘
      gaussianMix r = fun u => inner (𝕜 := ℝ) (gaussianMixRow r i) u := by
  funext u
  fin_cases i <;> simp [gaussianMix,gaussianMixRow,PiLp.inner_apply,Fin.sum_univ_two]
  ring

theorem map_gaussianMix {r : ℝ} (hr : r∈Icc (-1) 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin 2))).map (gaussianMix r)=
      multivariateGaussian 0 (bivariateCorrelation r) := by
  have hs : 0≤1-r^2 := by nlinarith [hr.1,hr.2]
  have hsq := Real.sq_sqrt hs
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map,integral_id_stdGaussian,map_zero,integral_id_multivariateGaussian]
    exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis fun i j => ?_
  rw [ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov,covariance_map]
  · rw [gaussianMix_inner,gaussianMix_inner,
      ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,innerSL_apply_apply,
      covarianceBilin_multivariateGaussian (bivariateCorrelation_posSemidef hr)]
    simp only [PiLp.inner_apply]
    fin_cases i <;> fin_cases j <;>
      simp [gaussianMixRow,bivariateCorrelation,Fin.sum_univ_two]
    nlinarith
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

theorem gaussianBivariate_toMeasure_independent {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).toMeasure =
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)).map
        (fun x => ![cdfUnit (gaussianReal 0 1) (x 0),
          cdfUnit (gaussianReal 0 1) (r*x 0+Real.sqrt (1-r^2)*x 1)]) := by
  change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).map
    (fun x i => cdfUnit (gaussianReal 0 1) (x i))=_
  rw [← map_gaussianMix hr,← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x i
  fin_cases i <;> simp [Function.comp_def,gaussianMix]

theorem gaussianBivariate_rho_normal_integral {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).spearmanRho =
      12*(∫ x : Fin 2 → ℝ, ProbabilityTheory.cdf (gaussianReal 0 1) (x 0)*
        ProbabilityTheory.cdf (gaussianReal 0 1) (r*x 0+Real.sqrt (1-r^2)*x 1)
        ∂Measure.pi (fun _ => gaussianReal 0 1))-3 := by
  have hm : Measurable (fun x : Fin 2 → ℝ => ![cdfUnit (gaussianReal 0 1) (x 0),
      cdfUnit (gaussianReal 0 1) (r*x 0+Real.sqrt (1-r^2)*x 1)]) := by fun_prop
  have hg : Measurable (fun u : Fin 2 → I => (u 0:ℝ)*(u 1:ℝ)) := by fun_prop
  rw [spearmanRho,gaussianBivariate_toMeasure_independent hr,
    integral_map hm.aemeasurable hg.aestronglyMeasurable]
  rfl

end Verification
