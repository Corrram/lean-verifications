import Verification.HuslerReissFormula

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem huslerReiss_pickands_interior (δ : ℝ) (hδ : 0<δ) (t : I)
    (ht : (t:ℝ)∈Ioo (0:ℝ) 1) :
    Verification.copulaPickands (Verification.huslerReissPositive δ hδ) t=
      (1-(t:ℝ))*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((1-(t:ℝ))/(t:ℝ)))+
      (t:ℝ)*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((t:ℝ)/(1-(t:ℝ)))) := by
  rw [Verification.huslerReissPositive,Verification.stableTailCopula_pickands]
  exact Verification.huslerReissStableTail_formula δ _ _ hδ (by linarith [ht.2]) ht.1

theorem huslerReiss_cdf_interior (δ : ℝ) (hδ : 0<δ) (u v : I)
    (hu : (u:ℝ)∈Ioo (0:ℝ) 1) (hv : (v:ℝ)∈Ioo (0:ℝ) 1) :
    (Verification.huslerReissPositive δ hδ).cdf ![u,v]=Real.exp (-(
      (-Real.log (u:ℝ))*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((-Real.log (u:ℝ))/(-Real.log (v:ℝ))))+
      (-Real.log (v:ℝ))*ProbabilityTheory.cdf (gaussianReal 0 1)
        (1/δ+δ/2*Real.log ((-Real.log (v:ℝ))/(-Real.log (u:ℝ)))))) := by
  rw [Verification.huslerReissPositive,Verification.stableTailCopula_cdf,Verification.stableTailCDF_positive_coords _ _ _ hu.1 hv.1,
    Verification.huslerReissStableTail_formula δ _ _ hδ
      (neg_pos.mpr (Real.log_neg hu.1 hu.2)) (neg_pos.mpr (Real.log_neg hv.1 hv.2))]

end Papers.AnsariRockel2024
