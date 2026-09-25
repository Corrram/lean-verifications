import Verification.TEVConstruction

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem tEV_spectral_isExtremeValue (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) :
    (Verification.tEV ν r hν hr).IsExtremeValue := Verification.tEV_isExtremeValue ν r hν hr

theorem tEV_spectral_isCI (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) :
    (Verification.tEV ν r hν hr).IsCI := Verification.tEV_isCI ν r hν hr

theorem tEV_pickands_spectral (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) (t : I) :
    Verification.copulaPickands (Verification.tEV ν r hν hr) t=
      ∫ z : EuclideanSpace ℝ (Fin 2),max ((1-(t:ℝ))*Verification.gaussianPositiveWeight ν (z 0))
        ((t:ℝ)*Verification.gaussianPositiveWeight ν (z 1))
          ∂multivariateGaussian 0 (Verification.bivariateCorrelation r) :=
  Verification.tEV_pickands_spectral ν r hν hr t

end Papers.AnsariRockel2024
