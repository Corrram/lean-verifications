import Verification.GaussianDifference

/-! # Differences of centered Gaussian pairs with different correlations -/

open ProbabilityTheory MeasureTheory Set

namespace Verification

theorem charFun_bivariateGaussian {r : ℝ} (hr : r∈Icc (-1) 1)
    (t : EuclideanSpace ℝ (Fin 2)) :
    charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)) t=
      Complex.exp (-((t 0)^2+2*r*t 0*t 1+(t 1)^2 : ℝ)/2) := by
  rw [charFun_multivariateGaussian (bivariateCorrelation_posSemidef hr)]
  congr 1
  simp [bivariateCorrelation,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  ring

theorem map_gaussianDifference_mixed {r s : ℝ} (hr : r∈Icc (-1) 1) (hs : s∈Icc (-1) 1) :
    ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) (bivariateCorrelation r)).prod
      (multivariateGaussian 0 (bivariateCorrelation s))).map gaussianDifference=
      multivariateGaussian 0 (bivariateCorrelation ((r+s)/2)) := by
  have havg : (r+s)/2∈Icc (-1) 1 := by constructor <;> linarith [hr.1,hr.2,hs.1,hs.2]
  apply Measure.ext_of_charFunDual
  funext L
  have h1 : (L.comp gaussianDifference).comp (.inl ℝ _ _)=(Real.sqrt 2)⁻¹ • L := by
    ext x
    simp [gaussianDifference]
  have h2 : (L.comp gaussianDifference).comp (.inr ℝ _ _)=(-(Real.sqrt 2)⁻¹) • L := by
    ext x
    simp [gaussianDifference]
  have hc : ((Real.sqrt 2)⁻¹)^2=(1:ℝ)/2 := by
    rw [inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  rw [charFunDual_map,charFunDual_prod,h1,h2,
    ← charFun_toDual_symm_eq_charFunDual,← charFun_toDual_symm_eq_charFunDual,
    ← charFun_toDual_symm_eq_charFunDual,
    charFun_bivariateGaussian hr,charFun_bivariateGaussian hs,charFun_bivariateGaussian havg,
    ← Complex.exp_add]
  congr 1
  simp only [map_smul,PiLp.smul_apply,smul_eq_mul]
  push_cast
  have hc' : (((Real.sqrt 2)⁻¹ : ℝ):ℂ)^2=(1:ℂ)/2 := by
    rw [← Complex.ofReal_pow,hc]
    norm_num
  push_cast at hc'
  ring_nf
  rw [hc']
  ring

end Verification
