import Verification.LognormalSpectralIntegral
import Verification.GaussianReflection

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem huslerReissStableTail_formula (δ x y : ℝ) (hδ : 0<δ) (hx : 0<x) (hy : 0<y) :
    (huslerReissStableTail δ).value x y=
      x*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ+δ/2*Real.log (x/y))+
      y*ProbabilityTheory.cdf (gaussianReal 0 1) (1/δ+δ/2*Real.log (y/x)) := by
  let b := 1/δ+δ/2*Real.log (y/x)
  have hb : x*lognormalSpectralWeight (2/δ) b=y := by
    unfold lognormalSpectralWeight
    have he : (2/δ)*b-(2/δ)^2/2=Real.log (y/x) := by
      dsimp [b]
      field_simp
      ring
    rw [he,Real.exp_log (div_pos hy hx)]
    field_simp
  change (∫ z,max (x*lognormalSpectralWeight (2/δ) z) (y*1) ∂gaussianReal 0 1)=_
  simp only [mul_one]
  rw [lognormalSpectral_max_integral (2/δ) x y b (div_pos (by norm_num) hδ) hx hb]
  have he : -(b-2/δ)=1/δ+δ/2*Real.log (x/y) := by
    dsimp [b]
    rw [Real.log_div hx.ne' hy.ne',Real.log_div hy.ne' hx.ne']
    ring
  rw [← standardNormalCDF_neg,he]
  exact add_comm _ _

theorem huslerReissPositive_pickands_formula (δ : ℝ) (hδ : 0<δ) (t : I)
    (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    copulaPickands (huslerReissPositive δ hδ) t=
      (1-(t:ℝ))*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((1-(t:ℝ))/(t:ℝ)))+
      (t:ℝ)*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((t:ℝ)/(1-(t:ℝ)))) := by
  rw [huslerReissPositive,stableTailCopula_pickands]
  exact huslerReissStableTail_formula δ _ _ hδ (by linarith [ht.2]) ht.1

theorem huslerReissPositive_cdf_interior (δ : ℝ) (hδ : 0<δ) (u v : I)
    (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (huslerReissPositive δ hδ).cdf ![u,v]=Real.exp (-(
      (-Real.log (u:ℝ))*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((-Real.log (u:ℝ))/(-Real.log (v:ℝ))))+
      (-Real.log (v:ℝ))*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((-Real.log (v:ℝ))/(-Real.log (u:ℝ)))))) := by
  rw [huslerReissPositive,stableTailCopula_cdf,stableTailCDF_positive_coords _ _ _ hu.1 hv.1,
    huslerReissStableTail_formula δ _ _ hδ
      (neg_pos.mpr (Real.log_neg hu.1 hu.2)) (neg_pos.mpr (Real.log_neg hv.1 hv.2))]

end Verification
