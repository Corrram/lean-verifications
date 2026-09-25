import Verification.GaussianRepresentation
import Copula.Families.StudentT
import Copula.Support

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def studentBivariate (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) : Copula 2 :=
  studentT (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
    (by intro i; fin_cases i <;> rfl) ν hν

theorem studentBivariate_isSklarCopula (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    IsSklarCopula (studentTLaw (bivariateCorrelation r) ν hν) (studentBivariate r hr ν hν) :=
  isSklarCopula_studentT _ _ _ _ _

theorem ofContinuousMarginals_comonotonic_of_ae_eq (μ : ProbabilityMeasure (Fin 2 → ℝ))
    (hc : ∀ i, Continuous (ProbabilityTheory.cdf (marginal μ i)))
    (he : ∀ᵐ x ∂μ.toMeasure, x 0=x 1) : ofContinuousMarginals μ hc=comonotonic 2 := by
  have hm : marginal μ 0=marginal μ 1 := Measure.map_congr he
  apply (eq_comonotonic_iff_ae_eval_eq _).mpr
  change ∀ᵐ x ∂μ.toMeasure.map (marginalTransform μ),x 0=x 1
  apply (ae_map_iff (measurable_marginalTransform μ).aemeasurable
    (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1))).mpr
  filter_upwards [he] with x hx
  dsimp only [marginalTransform]
  rw [hm,hx]

theorem gaussian_one_ae_equal :
    ∀ᵐ x ∂multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation 1),x 0=x 1 := by
  rw [← map_gaussianMix (r := 1) (by norm_num)]
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
  exact Filter.Eventually.of_forall fun x => by simp [gaussianMix]

theorem gaussianScaleMixture_one (μ : ProbabilityMeasure ℝ) (s : ℝ → ℝ) (hs : Measurable s)
    (hp : ∀ᵐ t ∂μ.toMeasure,0<s t) :
    gaussianScaleMixture (bivariateCorrelation 1) (bivariateCorrelation_posSemidef (by norm_num))
      (by intro i; fin_cases i <;> rfl) μ s hs hp=comonotonic 2 := by
  apply ofContinuousMarginals_comonotonic_of_ae_eq
  change ∀ᵐ x ∂((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation 1)).prod
    μ.toMeasure).map (fun p i => s p.2*p.1 i),x 0=x 1
  apply (ae_map_iff (by fun_prop)
    (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1))).mpr
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun (by fun_prop) (by fun_prop))).mpr
  filter_upwards [gaussian_one_ae_equal] with x hx
  exact Filter.Eventually.of_forall fun t => by change s t*x 0=s t*x 1; rw [hx]

theorem studentBivariate_one (ν : ℝ) (hν : 0<ν) :
    studentBivariate 1 (by norm_num) ν hν=comonotonic 2 :=
  gaussianScaleMixture_one _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

end Verification
