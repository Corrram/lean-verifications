import Verification.ScaleMixtureDensity
import Papers.AnsariRockel2024.Student
import Papers.AnsariRockel2024.Laplace

open ProbabilityTheory MeasureTheory Set Copula

namespace Papers.AnsariRockel2024

theorem student_marginal_withDensity (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i=
      volume.withDensity (Verification.normalScaleMixtureDensity (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹)) := by
  unfold studentTLaw
  rw [Verification.gaussianScaleMixtureLaw_marginal _ (Verification.bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹) (by fun_prop) i]
  exact Verification.normalScaleMixtureMarginal_withDensity (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹) (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem student_marginal_equivalent_volume (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i ≪ volume ∧
      volume ≪ marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i := by
  unfold studentTLaw
  rw [Verification.gaussianScaleMixtureLaw_marginal _ (Verification.bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹) (by fun_prop) i]
  exact Verification.normalScaleMixtureMarginal_equivalent_volume (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹) (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem laplace_marginal_withDensity (r : ℝ) (hr : r∈Icc (-1) 1) (i : Fin 2) :
    marginal (gaussianScaleMixtureLaw (Verification.bivariateCorrelation r) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt) i=
      volume.withDensity (Verification.normalScaleMixtureDensity (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt) := by
  rw [Verification.gaussianScaleMixtureLaw_marginal _ (Verification.bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop) i]
  exact Verification.normalScaleMixtureMarginal_withDensity (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop) Verification.laplace_scale_pos

theorem laplace_marginal_equivalent_volume (r : ℝ) (hr : r∈Icc (-1) 1) (i : Fin 2) :
    marginal (gaussianScaleMixtureLaw (Verification.bivariateCorrelation r) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt) i ≪ volume ∧
      volume ≪ marginal (gaussianScaleMixtureLaw (Verification.bivariateCorrelation r) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt) i := by
  rw [Verification.gaussianScaleMixtureLaw_marginal _ (Verification.bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop) i]
  exact Verification.normalScaleMixtureMarginal_equivalent_volume (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop) Verification.laplace_scale_pos

end Papers.AnsariRockel2024
