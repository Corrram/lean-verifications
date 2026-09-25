import Verification.StudentJointDensity
import Verification.ScaleMixtureJointDensity
import Verification.StudentMarginalDensity
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

theorem student_marginal_standard_density (r : ℝ) (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    marginal (studentTLaw (Verification.bivariateCorrelation r) ν hν) i=
      volume.withDensity (fun x : ℝ => ENNReal.ofReal
        (Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))*
          (1+x^2/ν)^(-((ν+1)/2)))) := by
  rw [student_marginal_withDensity r hr ν hν i]
  congr 1
  funext x
  rw [Verification.student_marginal_density_evaluation ν hν x,
    Verification.studentMarginalPDF_standard_form hν x]

theorem student_joint_withDensity (r : ℝ) (hr : r∈Ioo (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (studentTLaw (Verification.bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow=
      volume.withDensity (Verification.gaussianScaleMixtureJointDensity r (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹)) :=
  Verification.gaussianScaleMixtureLaw_joint_withDensity hr (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹) (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem student_joint_equivalent_volume (r : ℝ) (hr : r∈Ioo (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (studentTLaw (Verification.bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow ≪ volume ∧
      volume ≪ (studentTLaw (Verification.bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow :=
  Verification.gaussianScaleMixtureLaw_joint_equivalent_volume hr (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t : ℝ => (Real.sqrt t)⁻¹) (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem laplace_joint_withDensity (r : ℝ) (hr : r∈Ioo (-1) 1) :
    (gaussianScaleMixtureLaw (Verification.bivariateCorrelation r) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt).toMeasure.map MeasurableEquiv.finTwoArrow=
      volume.withDensity (Verification.gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt) :=
  Verification.gaussianScaleMixtureLaw_joint_withDensity hr (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop) Verification.laplace_scale_pos

theorem laplace_joint_equivalent_volume (r : ℝ) (hr : r∈Ioo (-1) 1) :
    (gaussianScaleMixtureLaw (Verification.bivariateCorrelation r) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt).toMeasure.map MeasurableEquiv.finTwoArrow ≪ volume ∧
      volume ≪ (gaussianScaleMixtureLaw (Verification.bivariateCorrelation r) (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt).toMeasure.map MeasurableEquiv.finTwoArrow :=
  Verification.gaussianScaleMixtureLaw_joint_equivalent_volume hr (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (by fun_prop) Verification.laplace_scale_pos

theorem student_joint_standard_density (r : ℝ) (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (studentTLaw (Verification.bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow=
      volume.withDensity (fun p : ℝ×ℝ => ENNReal.ofReal
        ((2*Real.pi*Real.sqrt (1-r^2))⁻¹*
          (1+(p.1^2-2*r*p.1*p.2+p.2^2)/(ν*(1-r^2)))^(-((ν+2)/2)))) := by
  rw [student_joint_withDensity r hr ν hν]
  congr 1
  funext p
  rw [Verification.student_joint_density_evaluation hr ν hν p,
    Verification.studentJointPDF_standard_form hr hν p,
    Verification.studentQuadratic_standard_form hr p]
  congr 1
  rw [show -(ν/2+1)=-((ν+2)/2) by ring]
  congr 2
  rw [div_div,mul_comm (1-r^2) ν]

end Papers.AnsariRockel2024
