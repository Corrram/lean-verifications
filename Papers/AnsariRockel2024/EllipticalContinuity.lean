import Verification.ScaleMixtureContinuity
import Papers.AnsariRockel2024.Student
import Papers.AnsariRockel2024.Laplace

open ProbabilityTheory MeasureTheory Set Copula Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem student_cdf_continuous (ν : ℝ) (hν : 0<ν) (u : Fin 2 → I) :
    Continuous (fun r : Icc (-1:ℝ) 1 => (Verification.studentBivariate r r.property ν hν).cdf u) :=
  Verification.gaussianScaleMixture_cdf_continuous
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) u

theorem laplace_cdf_continuous (u : Fin 2 → I) :
    Continuous (fun r : Icc (-1:ℝ) 1 => (Verification.laplaceBivariate r r.property).cdf u) :=
  Verification.gaussianScaleMixture_cdf_continuous _ _ (by fun_prop) Verification.laplace_scale_pos u

theorem student_cdf_tendsto_one (ν : ℝ) (hν : 0<ν) (u : Fin 2 → I) :
    Tendsto (fun r : Icc (-1:ℝ) 1 => (Verification.studentBivariate r r.property ν hν).cdf u)
      (𝓝 (⟨1,by norm_num⟩ : Icc (-1:ℝ) 1)) (𝓝 ((comonotonic 2).cdf u)) := by
  simpa only [student_one ν hν] using
    (student_cdf_continuous ν hν u).tendsto (⟨1,by norm_num⟩ : Icc (-1:ℝ) 1)

theorem student_cdf_tendsto_negative_one (ν : ℝ) (hν : 0<ν) (u : Fin 2 → I) :
    Tendsto (fun r : Icc (-1:ℝ) 1 => (Verification.studentBivariate r r.property ν hν).cdf u)
      (𝓝 (⟨-1,by norm_num⟩ : Icc (-1:ℝ) 1)) (𝓝 (countermonotonic.cdf u)) := by
  simpa only [student_negative_one ν hν] using
    (student_cdf_continuous ν hν u).tendsto (⟨-1,by norm_num⟩ : Icc (-1:ℝ) 1)

theorem laplace_cdf_tendsto_one (u : Fin 2 → I) :
    Tendsto (fun r : Icc (-1:ℝ) 1 => (Verification.laplaceBivariate r r.property).cdf u)
      (𝓝 (⟨1,by norm_num⟩ : Icc (-1:ℝ) 1)) (𝓝 ((comonotonic 2).cdf u)) := by
  simpa only [laplace_one] using
    (laplace_cdf_continuous u).tendsto (⟨1,by norm_num⟩ : Icc (-1:ℝ) 1)

theorem laplace_cdf_tendsto_negative_one (u : Fin 2 → I) :
    Tendsto (fun r : Icc (-1:ℝ) 1 => (Verification.laplaceBivariate r r.property).cdf u)
      (𝓝 (⟨-1,by norm_num⟩ : Icc (-1:ℝ) 1)) (𝓝 (countermonotonic.cdf u)) := by
  simpa only [laplace_negative_one] using
    (laplace_cdf_continuous u).tendsto (⟨-1,by norm_num⟩ : Icc (-1:ℝ) 1)

end Papers.AnsariRockel2024
