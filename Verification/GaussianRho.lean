import Verification.GaussianMixedDifference

/-! # Gaussian Spearman rho

Comparison with an independent copula reduces rho to the lower-quadrant
probability of a centered Gaussian pair with half the original correlation.
-/

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

theorem gaussianBivariate_comparison_probability {r s : ℝ}
    (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    ((gaussianBivariate r hr).toMeasure.prod (gaussianBivariate s hs).toMeasure).real
      {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}=
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2))
        (bivariateCorrelation ((r+s)/2))).real {x | x 0≤0 ∧ x 1≤0} := by
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation s)
  let f := fun x : EuclideanSpace ℝ (Fin 2) => fun i => cdfUnit (gaussianReal 0 1) (x i)
  have hf : Measurable f := by fun_prop
  have hC : (gaussianBivariate r hr).toMeasure=μ.map f := rfl
  have hD : (gaussianBivariate s hs).toMeasure=ν.map f := rfl
  have hS : MeasurableSet {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hQ : MeasurableSet {x : EuclideanSpace ℝ (Fin 2) | x 0≤0 ∧ x 1≤0} := by
    apply MeasurableSet.inter
    · exact measurableSet_le
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 0) by fun_prop) measurable_const
    · exact measurableSet_le
        (show Measurable (fun x : EuclideanSpace ℝ (Fin 2) => x 1) by fun_prop) measurable_const
  have hset : (Prod.map f f) ⁻¹' {p : (Fin 2 → I)×(Fin 2 → I) | p.1≤p.2}=
      gaussianDifference ⁻¹' {x | x 0≤0 ∧ x 1≤0} := by
    ext p
    change (∀ i, ProbabilityTheory.cdf (gaussianReal 0 1) (p.1 i)≤
      ProbabilityTheory.cdf (gaussianReal 0 1) (p.2 i)) ↔
      (Real.sqrt 2)⁻¹*(p.1 0-p.2 0)≤0 ∧ (Real.sqrt 2)⁻¹*(p.1 1-p.2 1)≤0
    have hc : 0<(Real.sqrt 2)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by norm_num))
    have hh (a b : ℝ) : (Real.sqrt 2)⁻¹*(a-b)≤0 ↔ a≤b := by
      constructor
      · intro h
        nlinarith
      · intro h
        exact mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr h)
    simp only [standardNormalCDF_strictMono.le_iff_le,Fin.forall_fin_two,hh]
  rw [hC,hD,Measure.map_prod_map _ _ hf hf,
    map_measureReal_apply (hf.prodMap hf) hS,hset,
    ← map_measureReal_apply (by fun_prop) hQ,map_gaussianDifference_mixed hr hs]

theorem gaussianBivariate_spearmanRho {r : ℝ} (hr : r∈Icc (-1) 1) :
    (gaussianBivariate r hr).spearmanRho=6/Real.pi*Real.arcsin (r/2) := by
  rw [spearmanRho_probability,← gaussianBivariate_zero,
    gaussianBivariate_comparison_probability (by norm_num) hr,zero_add,
    multivariateGaussian_lower_quadrant (show r/2∈Ioo (-1) 1 by
      constructor <;> linarith [hr.1,hr.2])]
  ring

end Verification
