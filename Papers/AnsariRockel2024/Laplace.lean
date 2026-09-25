import Copula.Families.ScaleMixtures
import Verification.ScaleMixtureTau
import Verification.ScaleMixtureJointCDF
import Verification.ScaleMixtureReflection
import Verification.StudentNegativeEndpoint

open ProbabilityTheory MeasureTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def laplaceBivariate (r : ℝ) (hr : r∈Icc (-1) 1) : Copula 2 :=
  laplace (bivariateCorrelation r) (bivariateCorrelation_posSemidef hr)
    (by intro i; fin_cases i <;> rfl)

theorem laplace_scale_pos : ∀ᵐ t ∂(gammaProbability 1 1 zero_lt_one zero_lt_one).toMeasure,
    0<Real.sqrt t := by
  filter_upwards [ae_pos_gammaMeasure 1 1] with t ht
  exact Real.sqrt_pos.mpr ht

end Verification

namespace Papers.AnsariRockel2024

open Verification

theorem laplace_isSklarCopula (r : ℝ) (hr : r∈Icc (-1) 1) :
    IsSklarCopula (gaussianScaleMixtureLaw (bivariateCorrelation r)
      (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt) (laplaceBivariate r hr) :=
  isSklarCopula_gaussianScaleMixture _ (bivariateCorrelation_posSemidef hr)
    (by intro i; fin_cases i <;> rfl) _ _ (by fun_prop) laplace_scale_pos

theorem laplace_one : laplaceBivariate 1 (by norm_num)=comonotonic 2 :=
  gaussianScaleMixture_one _ _ (by fun_prop) laplace_scale_pos

theorem laplace_negative_one : laplaceBivariate (-1) (by norm_num)=countermonotonic :=
  gaussianScaleMixture_negative_one _ _ (by fun_prop) laplace_scale_pos

theorem laplace_kendallTau (r : ℝ) (hr : r∈Icc (-1) 1) :
    (laplaceBivariate r hr).kendallTau=2/Real.pi*Real.arcsin r :=
  gaussianScaleMixture_kendallTau hr _ _ (by fun_prop) laplace_scale_pos

theorem laplace_lowerOrthant_monotone {r q : ℝ} (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1)
    (hrq : r≤q) : (laplaceBivariate r hr).LowerOrthantLE (laplaceBivariate q hq) :=
  gaussianScaleMixture_lowerOrthant hr hq hrq _ _ (by fun_prop) laplace_scale_pos

theorem laplace_lowerOrthant_iff {r q : ℝ} (hr : r∈Icc (-1) 1) (hq : q∈Icc (-1) 1) :
    (laplaceBivariate r hr).LowerOrthantLE (laplaceBivariate q hq) ↔ r≤q := by
  refine ⟨?_,fun h => laplace_lowerOrthant_monotone hr hq h⟩
  intro h
  have ht := h.kendallTau_le
  rw [laplace_kendallTau r hr,laplace_kendallTau q hq] at ht
  exact (Real.strictMonoOn_arcsin.le_iff_le hr hq).mp
    ((mul_le_mul_iff_right₀ (div_pos (by norm_num) Real.pi_pos)).mp ht)

theorem laplace_reflect_second {r : ℝ} (hr : r∈Icc (-1) 1) :
    laplaceBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])=
      (laplaceBivariate r hr).reflect {1} :=
  gaussianScaleMixture_neg hr _ _ (by fun_prop) laplace_scale_pos

theorem laplace_rho_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (laplaceBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).spearmanRho=
      -(laplaceBivariate r hr).spearmanRho := by
  rw [laplace_reflect_second hr,spearmanRho_reflect_second]

theorem laplace_tau_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (laplaceBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).kendallTau=
      -(laplaceBivariate r hr).kendallTau := by
  rw [laplace_reflect_second hr,kendallTau_reflect_second]

theorem laplace_xi_neg {r : ℝ} (hr : r∈Icc (-1) 1) :
    (laplaceBivariate (-r) (by constructor <;> linarith [hr.1,hr.2])).chatterjeeXi=
      (laplaceBivariate r hr).chatterjeeXi := by
  rw [laplace_reflect_second hr,xi_reflect_second]

end Papers.AnsariRockel2024
