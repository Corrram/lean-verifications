import Verification.GammaSupport
import Verification.ScaleMixtureContinuity
import Mathlib.Probability.Moments.Variance

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal unitInterval

namespace Verification

theorem gammaVariance_zero_ne_independence (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    gaussianScaleMixture (bivariateCorrelation 0) (bivariateCorrelation_posSemidef (by norm_num))
      (by intro i; fin_cases i <;> rfl) (gammaProbability a b ha hb) Real.sqrt (by fun_prop) (by
        filter_upwards [ae_pos_gammaMeasure a b] with t ht
        exact Real.sqrt_pos.mpr ht) ≠ independence 2 := by
  let μ := gammaProbability a b ha hb
  let f := fun t : ℝ => ProbabilityTheory.cdf (gaussianReal 0 1) (1/Real.sqrt t)
  have hp : ∀ᵐ t ∂μ.toMeasure,0<Real.sqrt t := by
    filter_upwards [ae_pos_gammaMeasure a b] with t ht
    exact Real.sqrt_pos.mpr ht
  have hm : Measurable f := (monotone_cdf (gaussianReal 0 1)).measurable.comp (by fun_prop)
  have hmem : MemLp f 2 μ.toMeasure := MemLp.of_bound hm.aestronglyMeasurable 1 (by
    exact Filter.Eventually.of_forall fun t => by
      dsimp only [f]
      rw [Real.norm_eq_abs,abs_of_nonneg (ProbabilityTheory.cdf_nonneg _ _)]
      exact ProbabilityTheory.cdf_le_one _ _)
  intro hind
  have h := gaussianScaleMixture_cdf_marginal (r := 0) (by norm_num) μ Real.sqrt (by fun_prop) hp 1 1
  rw [hind] at h
  simp only [gaussianBivariate_zero,cdf_independence,Fin.prod_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one] at h
  change ProbabilityTheory.cdf (normalScaleMixtureMarginal μ Real.sqrt) 1*
    ProbabilityTheory.cdf (normalScaleMixtureMarginal μ Real.sqrt) 1=
    ∫ t, f t*f t ∂μ.toMeasure at h
  simp only [← pow_two] at h
  rw [normalScaleMixtureMarginal_cdf μ Real.sqrt (by fun_prop) hp] at h
  have hv : variance f μ.toMeasure=0 := by
    rw [variance_eq_sub hmem]
    simp only [Pi.pow_apply]
    rw [← h]
    exact sub_self _
  have he := ae_eq_integral_of_variance_eq_zero hmem hv
  have hc : ContinuousOn f (Ioi 0) := by
    apply continuous_standardNormalCDF.comp_continuousOn
    apply ContinuousOn.div continuousOn_const Real.continuous_sqrt.continuousOn
    intro t ht
    exact (Real.sqrt_pos.mpr ht).ne'
  have hall := gamma_ae_eq_constant_of_continuousOn ha hb hc he
  have heq : f 1=f 4 := (hall 1 (by norm_num)).trans (hall 4 (by norm_num)).symm
  have harg := standardNormalCDF_strictMono.injective heq
  norm_num [f,Real.sqrt_eq_iff_eq_sq] at harg

end Verification
