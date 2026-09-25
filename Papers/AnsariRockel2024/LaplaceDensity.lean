import Verification.LaplaceTP2Witness

open ProbabilityTheory MeasureTheory Real Set Copula Verification
open scoped ENNReal

namespace Papers.AnsariRockel2024

/-- The actual Laplace joint law, with its Gaussian variance mixture evaluated
as a one-dimensional radial integral. -/
theorem laplace_joint_radial_density (r : ℝ) (hr : r∈Ioo (-1) 1) :
    (gaussianScaleMixtureLaw (bivariateCorrelation r)
      (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt).toMeasure.map
        MeasurableEquiv.finTwoArrow=
    (volume : Measure (ℝ×ℝ)).withDensity (fun p =>
      ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*
        laplaceRadialDensity ((p.1^2-2*r*p.1*p.2+p.2^2)/(1-r^2))) := by
  simpa only [studentQuadratic_standard_form hr] using laplace_joint_radial_withDensity hr

theorem laplace_radial_density_antitone : Antitone laplaceRadialDensity :=
  laplaceRadialDensity_antitone

theorem laplace_radial_density_finite {q : ℝ} (hq : 0<q) :
    laplaceRadialDensity q≠∞ := laplaceRadialDensity_ne_top hq

theorem laplace_radial_density_origin : laplaceRadialDensity 0=∞ :=
  laplaceRadialDensity_zero

theorem laplace_radial_density_blowup :
    Filter.Tendsto laplaceRadialDensity (nhds (0:ℝ)) (nhds ∞) :=
  laplaceRadialDensity_tendsto_zero

theorem laplace_radial_density_continuous {q : ℝ} (hq : 0<q) :
    ContinuousAt laplaceRadialDensity q := laplaceRadialDensity_continuousAt hq

/-- A strict violation for the explicitly identified joint density. This statement
does not yet exclude every almost-everywhere equivalent density. -/
theorem laplace_joint_density_tp2_counterexample (r : ℝ) (hr : r∈Ioo (-1) 1) :
    ∃ t : ℝ, 0<t ∧ t<1 ∧
      gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (-1,0)*
        gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (t,1) <
      gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (-1,1)*
        gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt (t,0) :=
  laplace_joint_density_tp2_witness hr

end Papers.AnsariRockel2024
