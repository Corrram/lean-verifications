import Verification.StudentMarginalDensity
import Verification.ScaleMixtureJointDensity

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem gaussianPDFReal_scaled_inverse_sqrt {t c : ℝ} (ht : 0<t) (hc : 0<c) (m x : ℝ) :
    gaussianPDFReal m (NNReal.mk (((Real.sqrt t)⁻¹*c)^2) (sq_nonneg _)) x=
      (Real.sqrt (2*Real.pi))⁻¹*c⁻¹*Real.sqrt t*Real.exp (-(((x-m)^2/(2*c^2))*t)) := by
  have hroot : Real.sqrt (2*Real.pi*((Real.sqrt t)⁻¹*c)^2)=
      Real.sqrt (2*Real.pi)*c/Real.sqrt t := by
    rw [Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,abs_mul,abs_inv,
      abs_of_pos (Real.sqrt_pos.mpr ht),abs_of_pos hc]
    ring
  have he : -(x-m)^2/(2*((Real.sqrt t)⁻¹*c)^2)=-(((x-m)^2/(2*c^2))*t) := by
    rw [mul_pow,inv_pow,Real.sq_sqrt ht.le]
    field_simp
  simp only [gaussianPDFReal,NNReal.coe_mk,hroot,he]
  field_simp

noncomputable def studentQuadratic (r : ℝ) (p : ℝ×ℝ) : ℝ :=
  p.1^2+(p.2-r*p.1)^2/(1-r^2)

theorem studentQuadratic_nonneg {r : ℝ} (hr : r∈Ioo (-1) 1) (p : ℝ×ℝ) :
    0≤studentQuadratic r p := by
  have h : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  unfold studentQuadratic
  positivity

theorem student_gaussian_density_product {r t : ℝ} (hr : r∈Ioo (-1) 1) (ht : 0<t) (p : ℝ×ℝ) :
    gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) p.1*
      gaussianPDF (r*p.1) (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2=
    ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*
      ENNReal.ofReal (t^((1:ℝ))*Real.exp (-((studentQuadratic r p/2)*t))) := by
  have h : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  rw [gaussianPDF,gaussianPDF,gaussianPDFReal_inverse_sqrt ht,
    gaussianPDFReal_scaled_inverse_sqrt ht (Real.sqrt_pos.mpr h),
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.sqrt_eq_rpow,Real.sq_sqrt h.le,Real.rpow_one]
  have hex : Real.exp (-((studentQuadratic r p/2)*t))=
      Real.exp (-((p.1^2/2)*t))*Real.exp (-(((p.2-r*p.1)^2/(2*(1-r^2)))*t)) := by
    rw [← Real.exp_add]
    congr 1
    unfold studentQuadratic
    field_simp
    ring
  rw [hex]
  have hsq := Real.sq_sqrt ht.le
  have hpi := Real.sq_sqrt (show 0≤2*Real.pi by positivity)
  field_simp
  nlinarith

noncomputable def studentJointPDF (r ν : ℝ) (p : ℝ×ℝ) : ℝ :=
  (2*Real.pi*Real.sqrt (1-r^2))⁻¹*((ν/2)^(ν/2)/Real.Gamma (ν/2)*
    Real.Gamma (ν/2+1)/(ν/2+studentQuadratic r p/2)^(ν/2+1))

theorem student_joint_density_evaluation {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (p : ℝ×ℝ) :
    gaussianScaleMixtureJointDensity r
      (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity))
      (fun t => (Real.sqrt t)⁻¹) p=ENNReal.ofReal (studentJointPDF r ν p) := by
  have he : (fun t => gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) p.1*
      gaussianPDF (r*p.1) (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2)=ᵐ[gammaMeasure (ν/2) (ν/2)]
      fun t => ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*
        ENNReal.ofReal (t^((1:ℝ))*Real.exp (-((studentQuadratic r p/2)*t))) := by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact student_gaussian_density_product hr ht p
  unfold gaussianScaleMixtureJointDensity
  change (∫⁻ t, gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) p.1*
    gaussianPDF (r*p.1) (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2
      ∂gammaMeasure (ν/2) (ν/2))=_
  have hq := studentQuadratic_nonneg hr p
  rw [lintegral_congr_ae he,lintegral_const_mul _ (by
    unfold studentQuadratic
    fun_prop),lintegral_power_exp_gammaMeasure (by positivity) (by positivity) (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  rfl

theorem studentJointPDF_standard_form {r : ℝ} (hr : r∈Ioo (-1) 1)
    {ν : ℝ} (hν : 0<ν) (p : ℝ×ℝ) :
    studentJointPDF r ν p=(2*Real.pi*Real.sqrt (1-r^2))⁻¹*
      (1+studentQuadratic r p/ν)^(-(ν/2+1)) := by
  have ha : 0<ν/2 := by positivity
  have hq := studentQuadratic_nonneg hr p
  have hp : 0<1+studentQuadratic r p/ν := by positivity
  have hrate : ν/2+studentQuadratic r p/2=(ν/2)*(1+studentQuadratic r p/ν) := by field_simp
  rw [studentJointPDF,hrate,Real.mul_rpow ha.le hp.le,Real.rpow_add ha,Real.rpow_one,
    Real.Gamma_add_one ha.ne',Real.rpow_neg hp.le]
  have hpower := (Real.rpow_pos_of_pos ha (ν/2)).ne'
  have hG := (Real.Gamma_pos_of_pos ha).ne'
  field_simp

theorem studentQuadratic_standard_form {r : ℝ} (hr : r∈Ioo (-1) 1) (p : ℝ×ℝ) :
    studentQuadratic r p=(p.1^2-2*r*p.1*p.2+p.2^2)/(1-r^2) := by
  have h : 0<1-r^2 := by nlinarith [hr.1,hr.2]
  unfold studentQuadratic
  field_simp
  ring

end Verification
