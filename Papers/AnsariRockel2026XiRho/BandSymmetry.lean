import Papers.AnsariRockel2026XiRho.BandCoefficients
import Verification.XiPredictorReflection

/-! # Remark 3: radial symmetry and the negative-parameter family -/

open ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2026XiRho

/-- Every normalized band is radially symmetric, by uniqueness of its support optimizer. -/
theorem normalizedBand_radially_symmetric (b : ℝ) (hb : 0 ≤ b) :
    (normalizedBand b hb).IsRadiallySymmetric := by
  apply (normalizedBand_support_eq_iff _ b hb).mp
  rw [Copula.spearmanRho_survivalCopula, xi_survival]

theorem sourceBand_radially_symmetric (b : ℝ) (hb : 0 < b) :
    (sourceBand b hb).IsRadiallySymmetric := by
  rw [sourceBand_eq_normalizedBand]
  exact normalizedBand_radially_symmetric b hb.le

/-- Source equation (21), with the parameter magnitude represented as b>0. -/
noncomputable def negativeSourceBand (b : ℝ) (hb : 0 < b) : Copula 2 :=
  (sourceBand b hb).reflect {0}

theorem negativeSourceBand_cdf (b : ℝ) (hb : 0 < b) (u v : I) :
    (negativeSourceBand b hb).cdf ![u, v] =
      (v : ℝ) - (sourceBand b hb).cdf ![unitInterval.symm u, v] :=
  Copula.cdf_reflect_first _ u v

theorem negativeSourceBand_coefficients (b : ℝ) (hb : 0 < b) :
    (negativeSourceBand b hb).chatterjeeXi = bandXi b ∧
      (negativeSourceBand b hb).spearmanRho = -bandRho b := by
  unfold negativeSourceBand
  rw [xi_reflect_first, Copula.spearmanRho_reflect_first, sourceBand_xi, sourceBand_rho]
  exact ⟨rfl, rfl⟩

/-- For the radially symmetric source family either single-coordinate reflection agrees. -/
theorem negativeSourceBand_eq_response_reflection (b : ℝ) (hb : 0 < b) :
    negativeSourceBand b hb = (sourceBand b hb).reflect {1} := by
  have h : ((sourceBand b hb).reflect {0}).reflect {1} = sourceBand b hb := by
    rw [Copula.reflect_first_second]
    exact sourceBand_radially_symmetric b hb
  simpa only [negativeSourceBand, Copula.reflect_reflect] using
    congrArg (fun D : Copula 2 => D.reflect {1}) h

end Papers.AnsariRockel2026XiRho
