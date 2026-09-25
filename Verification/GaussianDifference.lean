import Verification.GaussianQuadrant
import Verification.KendallProbability

/-! # Stability of centered Gaussian differences

The characteristic function proves that the difference of two independent
copies, divided by sqrt(2), has the original law. No density assumption is
needed, so singular covariance matrices are included.
-/

open MeasureTheory ProbabilityTheory Set

namespace Verification

noncomputable def gaussianDifference :
    (EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Real.sqrt 2)⁻¹ • (ContinuousLinearMap.fst ℝ _ _-ContinuousLinearMap.snd ℝ _ _)

theorem gaussianDifference_apply (p : EuclideanSpace ℝ (Fin 2)×EuclideanSpace ℝ (Fin 2)) :
    gaussianDifference p=(Real.sqrt 2)⁻¹ • (p.1-p.2) := rfl

theorem map_gaussianDifference (r : ℝ) :
    let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
    (μ.prod μ).map gaussianDifference=μ := by
  dsimp only
  let μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)
  change (μ.prod μ).map gaussianDifference=μ
  apply Measure.ext_of_charFunDual
  funext L
  have h1 : (L.comp gaussianDifference).comp (.inl ℝ _ _)=(Real.sqrt 2)⁻¹ • L := by
    ext x
    simp [gaussianDifference]
  have h2 : (L.comp gaussianDifference).comp (.inr ℝ _ _)=(-(Real.sqrt 2)⁻¹) • L := by
    ext x
    simp [gaussianDifference]
  have hmean : ∫ x, id x ∂μ=0 := integral_id_multivariateGaussian
  have hc : ((Real.sqrt 2)⁻¹)^2=(1:ℝ)/2 := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  rw [charFunDual_map,charFunDual_prod,h1,h2]
  simp only [IsGaussian.charFunDual_eq',hmean,map_zero,Complex.ofReal_zero,zero_mul,
    zero_sub,map_smul,smul_apply,smul_eq_mul,Complex.ofReal_mul,
    Complex.ofReal_neg]
  rw [← Complex.exp_add]
  congr 1
  have hc' : (((Real.sqrt 2)⁻¹ : ℝ):ℂ)^2=(1:ℂ)/2 := by
    rw [← Complex.ofReal_pow,hc]
    norm_num
  calc
    _ = -(((((Real.sqrt 2)⁻¹ : ℝ):ℂ)^2) *
      (covarianceBilinDual μ L L : ℂ)) := by ring
    _ = _ := by rw [hc']; ring

end Verification
