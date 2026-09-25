import Verification.GaussianPositivePower
import Verification.GaussianBivariate
import Verification.StableTailExtremeValue

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

theorem bivariateGaussian_eval_preserving (r : ℝ) (hr : r∈Icc (-1) 1) (i : Fin 2) :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin 2) => z i)
      (multivariateGaussian 0 (bivariateCorrelation r)) (gaussianReal 0 1) := by
  have h := measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin 2))) (bivariateCorrelation_posSemidef hr) (i := i)
  fin_cases i <;> simpa [bivariateCorrelation] using h

theorem gaussianPositiveWeight_coordinate_integrable (ν r : ℝ) (hν : 0<ν)
    (hr : r∈Icc (-1) 1) (i : Fin 2) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) => gaussianPositiveWeight ν (z i))
      (multivariateGaussian 0 (bivariateCorrelation r)) :=
  (bivariateGaussian_eval_preserving r hr i).integrable_comp_of_integrable
    (gaussianPositiveWeight_integrable ν hν)

theorem gaussianPositiveWeight_coordinate_mean (ν r : ℝ) (hν : 0<ν)
    (hr : r∈Icc (-1) 1) (i : Fin 2) :
    (∫ z : EuclideanSpace ℝ (Fin 2),gaussianPositiveWeight ν (z i)
      ∂multivariateGaussian 0 (bivariateCorrelation r))=1 := by
  have hm := bivariateGaussian_eval_preserving r hr i
  have he := integral_map hm.measurable.aemeasurable
    ((hm.map_eq.symm ▸ gaussianPositiveWeight_integrable ν hν).aestronglyMeasurable)
  rw [hm.map_eq] at he
  rw [← he,gaussianPositiveWeight_mean ν hν]

noncomputable def tEVStableTail (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) : StableTail :=
  spectralStableTail (multivariateGaussian 0 (bivariateCorrelation r))
    (fun z => gaussianPositiveWeight ν (z 0)) (fun z => gaussianPositiveWeight ν (z 1))
    (gaussianPositiveWeight_coordinate_integrable ν r hν hr 0)
    (gaussianPositiveWeight_coordinate_integrable ν r hν hr 1)
    (fun _ => gaussianPositiveWeight_nonneg ν hν _) (fun _ => gaussianPositiveWeight_nonneg ν hν _)
    (gaussianPositiveWeight_coordinate_mean ν r hν hr 0)
    (gaussianPositiveWeight_coordinate_mean ν r hν hr 1)

noncomputable def tEV (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) : Copula 2 :=
  stableTailCopula (tEVStableTail ν r hν hr)

theorem tEV_isExtremeValue (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) :
    (tEV ν r hν hr).IsExtremeValue := stableTailCopula_isExtremeValue _

theorem tEV_isCI (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) :
    (tEV ν r hν hr).IsCI := stableTailCopula_isCI _

theorem tEV_pickands_spectral (ν r : ℝ) (hν : 0<ν) (hr : r∈Icc (-1) 1) (t : I) :
    copulaPickands (tEV ν r hν hr) t=
      ∫ z : EuclideanSpace ℝ (Fin 2),max ((1-(t:ℝ))*gaussianPositiveWeight ν (z 0))
        ((t:ℝ)*gaussianPositiveWeight ν (z 1)) ∂multivariateGaussian 0 (bivariateCorrelation r) := by
  rw [tEV,stableTailCopula_pickands]
  rfl

end Verification
