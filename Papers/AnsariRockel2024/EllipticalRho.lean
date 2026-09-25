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

end Papers.AnsariRockel2024
