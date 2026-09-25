import Papers.AnsariRockel2024.Student
import Verification.ScaleMixtureJointCDF
import Verification.ScaleMixtureTau

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

theorem student_joint_cdf (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) (a b : ℝ) :
    (studentTLaw (Verification.bivariateCorrelation r) ν hν).toMeasure.real (Iic ![a,b])=
      ∫ t, (Verification.gaussianBivariate r hr).cdf
        ![cdfUnit (gaussianReal 0 1) (a*Real.sqrt t),cdfUnit (gaussianReal 0 1) (b*Real.sqrt t)]
        ∂(gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)).toMeasure := by
  have h := Verification.gaussianScaleMixtureLaw_rectangle hr
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) a b
  simpa only [studentTLaw,div_inv_eq_mul] using h

theorem student_lowerOrthant_monotone {r q : ℝ} (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1)
    (hrq : r≤q) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).LowerOrthantLE (Verification.studentBivariate q hq ν hν) :=
  Verification.gaussianScaleMixture_lowerOrthant hr hq hrq
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem student_kendallTau (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).kendallTau=2/Real.pi*Real.arcsin r :=
  Verification.gaussianScaleMixture_kendallTau hr
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem student_lowerOrthant_iff {r q : ℝ} (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (Verification.studentBivariate r hr ν hν).LowerOrthantLE (Verification.studentBivariate q hq ν hν) ↔ r≤q := by
  refine ⟨?_,fun h => student_lowerOrthant_monotone hr hq h ν hν⟩
  intro h
  have ht := h.kendallTau_le
  rw [student_kendallTau r hr ν hν,student_kendallTau q hq ν hν] at ht
  exact (Real.strictMonoOn_arcsin.le_iff_le hr hq).mp
    ((mul_le_mul_iff_right₀ (div_pos (by norm_num) Real.pi_pos)).mp ht)

end Papers.AnsariRockel2024
