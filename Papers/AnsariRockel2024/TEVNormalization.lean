import Verification.GaussianPowerIntegral

open ProbabilityTheory MeasureTheory Real Set

namespace Papers.AnsariRockel2024

theorem tEV_gaussian_moment (ν : ℝ) (hν : 0<ν) :
    Verification.gaussianPositiveMoment ν=(Real.sqrt (2*Real.pi))⁻¹*
      ((2:ℝ)^((ν+1)/2)*Real.Gamma ((ν+1)/2)/2) :=
  Verification.gaussianPositiveMoment_formula ν hν

theorem tEV_gaussian_moment_add_two (ν : ℝ) (hν : 0<ν) :
    Verification.gaussianPositiveMoment (ν+2)=(ν+1)*Verification.gaussianPositiveMoment ν :=
  Verification.gaussianPositiveMoment_add_two ν hν

end Papers.AnsariRockel2024
