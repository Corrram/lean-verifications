import Verification.ScaleMixtureRho
import Papers.AnsariRockel2024.StudentOrder
import Papers.AnsariRockel2024.Laplace
import Verification.GaussianRhoNoise

open ProbabilityTheory MeasureTheory Set

namespace Papers.AnsariRockel2024

theorem elliptical_rho_conditional_comparison {r : ℝ} (hr : r∈Icc (-1) 1) (a b c : ℝ)
    (hab : 0<a^2+b^2) (hac : 0<a^2+c^2) :
    (((gaussianReal 0 1).prod (gaussianReal 0 1)).prod
      ((gaussianReal 0 1).prod (gaussianReal 0 1))).real
        {p | b*p.1.2≤a*p.1.1 ∧ c*p.2.2≤a*(r*p.1.1+Real.sqrt (1-r^2)*p.2.1)}=
      1/4+Real.arcsin (r*a^2/(Real.sqrt (a^2+b^2)*Real.sqrt (a^2+c^2)))/(2*Real.pi) :=
  Verification.gaussian_scaled_independent_comparison_arcsin hr a b c hab hac


theorem student_spearmanRho (r : ℝ) (hr : r∈Icc (-1) 1) (ν : ℝ) (hν : 0<ν) :
    let μ := gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)
    let s := fun t : ℝ => (Real.sqrt t)⁻¹
    (Verification.studentBivariate r hr ν hν).spearmanRho=
      6/Real.pi*(∫ a, ∫ t : ℝ×ℝ, Real.arcsin
        (r*(s a)^2/(Real.sqrt ((s a)^2+(s t.1)^2)*Real.sqrt ((s a)^2+(s t.2)^2)))
          ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure) :=
  Verification.gaussianScaleMixture_spearmanRho hr _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem laplace_spearmanRho (r : ℝ) (hr : r∈Icc (-1) 1) :
    let μ := gammaProbability 1 1 zero_lt_one zero_lt_one
    let s := Real.sqrt
    (Verification.laplaceBivariate r hr).spearmanRho=
      6/Real.pi*(∫ a, ∫ t : ℝ×ℝ, Real.arcsin
        (r*(s a)^2/(Real.sqrt ((s a)^2+(s t.1)^2)*Real.sqrt ((s a)^2+(s t.2)^2)))
          ∂μ.toMeasure.prod μ.toMeasure ∂μ.toMeasure) :=
  Verification.gaussianScaleMixture_spearmanRho hr _ _ (by fun_prop) Verification.laplace_scale_pos

end Papers.AnsariRockel2024
