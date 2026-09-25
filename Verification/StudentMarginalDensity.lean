import Copula.Families.StudentT
import Verification.ScaleMixtureDensity
import Verification.GammaPowerLaplace

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem gaussianPDFReal_inverse_sqrt {t : ℝ} (ht : 0<t) (x : ℝ) :
    gaussianPDFReal 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x=
      (Real.sqrt (2*Real.pi))⁻¹*t^((1:ℝ)/2)*Real.exp (-((x^2/2)*t)) := by
  have hsq : (Real.sqrt t)⁻¹^2=t⁻¹ := by rw [inv_pow,Real.sq_sqrt ht.le]
  simp only [gaussianPDFReal,NNReal.coe_mk,sub_zero,hsq]
  rw [Real.sqrt_mul (by positivity),Real.sqrt_inv,mul_inv,inv_inv,← Real.sqrt_eq_rpow]
  congr 2
  field_simp


noncomputable def studentMarginalPDF (ν x : ℝ) : ℝ :=
  (Real.sqrt (2*Real.pi))⁻¹*((ν/2)^(ν/2)/Real.Gamma (ν/2)*
    Real.Gamma (ν/2+1/2)/(ν/2+x^2/2)^(ν/2+1/2))

theorem studentMarginalPDF_pos {ν : ℝ} (hν : 0<ν) (x : ℝ) : 0<studentMarginalPDF ν x := by
  unfold studentMarginalPDF
  have hG := Real.Gamma_pos_of_pos (show 0<ν/2 by positivity)
  have hG' := Real.Gamma_pos_of_pos (show 0<ν/2+1/2 by positivity)
  positivity

theorem student_marginal_density_evaluation (ν : ℝ) (hν : 0<ν) (x : ℝ) :
    normalScaleMixtureDensity (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity))
      (fun t => (Real.sqrt t)⁻¹) x=ENNReal.ofReal (studentMarginalPDF ν x) := by
  have he : (fun t => gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x)=ᵐ[gammaMeasure (ν/2) (ν/2)]
      fun t => ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)*
        ENNReal.ofReal (t^((1:ℝ)/2)*Real.exp (-((x^2/2)*t))) := by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    rw [gaussianPDF,gaussianPDFReal_inverse_sqrt ht x,← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  unfold normalScaleMixtureDensity
  change (∫⁻ t, gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x
    ∂gammaMeasure (ν/2) (ν/2))=_
  rw [lintegral_congr_ae he,lintegral_const_mul _ (by fun_prop),
    lintegral_power_exp_gammaMeasure (by positivity) (by positivity) (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  rfl

theorem studentMarginalPDF_standard_form {ν : ℝ} (hν : 0<ν) (x : ℝ) :
    studentMarginalPDF ν x=Real.Gamma ((ν+1)/2)/(Real.sqrt (ν*Real.pi)*Real.Gamma (ν/2))*
      (1+x^2/ν)^(-((ν+1)/2)) := by
  have ha : 0<ν/2 := by positivity
  have hp : 0<1+x^2/ν := by positivity
  have hrate : ν/2+x^2/2=(ν/2)*(1+x^2/ν) := by field_simp
  have hroot : Real.sqrt (ν*Real.pi)=Real.sqrt (2*Real.pi)*Real.sqrt (ν/2) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    ring
  rw [show (ν+1)/2=ν/2+1/2 by ring,studentMarginalPDF,hrate,
    Real.mul_rpow ha.le hp.le,Real.rpow_add ha,← Real.sqrt_eq_rpow,
    Real.rpow_neg hp.le,hroot]
  have hpower := (Real.rpow_pos_of_pos ha (ν/2)).ne'
  field_simp

end Verification
