import Verification.HuslerReissConstruction
import Verification.GaussianNormalDensity

open ProbabilityTheory MeasureTheory Real Set Copula

namespace Verification

theorem lognormalSpectralWeight_pdf (s z : ℝ) :
    gaussianPDFReal 0 1 z*lognormalSpectralWeight s z=gaussianPDFReal s 1 z := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,lognormalSpectralWeight]
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem lognormalSpectralWeight_integral_Iic (s b : ℝ) :
    (∫ z in Iic b,lognormalSpectralWeight s z ∂gaussianReal 0 1)=
      ProbabilityTheory.cdf (gaussianReal 0 1) (b-s) := by
  rw [setIntegral_standardGaussian _ measurableSet_Iic]
  simp_rw [lognormalSpectralWeight_pdf]
  rw [← gaussianReal_cdf_density s b (by norm_num : (1:NNReal)≠0)]
  have h := standardNormal_affine_cdf s b (by norm_num : (0:ℝ)<1)
  simpa using h

theorem lognormalSpectralWeight_integral_Ioi (s b : ℝ) :
    (∫ z in Ioi b,lognormalSpectralWeight s z ∂gaussianReal 0 1)=
      1-ProbabilityTheory.cdf (gaussianReal 0 1) (b-s) := by
  have h := integral_add_compl (s := Iic b) measurableSet_Iic (lognormalSpectralWeight_integrable s)
  rw [compl_Iic,lognormalSpectralWeight_integral_Iic,lognormalSpectralWeight_mean] at h
  linarith

theorem lognormalSpectral_max_integral (s x y b : ℝ) (hs : 0<s) (hx : 0<x)
    (hb : x*lognormalSpectralWeight s b=y) :
    (∫ z,max (x*lognormalSpectralWeight s z) y ∂gaussianReal 0 1)=
      y*ProbabilityTheory.cdf (gaussianReal 0 1) b+
        x*(1-ProbabilityTheory.cdf (gaussianReal 0 1) (b-s)) := by
  have hi := (lognormalSpectralWeight_integrable s).const_mul x
  have hm : Integrable (fun z => max (x*lognormalSpectralWeight s z) y) (gaussianReal 0 1) :=
    hi.sup (integrable_const y)
  rw [← integral_add_compl (s := Iic b) measurableSet_Iic hm,compl_Iic]
  have hleft : (∫ z in Iic b,max (x*lognormalSpectralWeight s z) y ∂gaussianReal 0 1)=
      y*ProbabilityTheory.cdf (gaussianReal 0 1) b := by
    calc
      _ = ∫ _z in Iic b,y ∂gaussianReal 0 1 := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro z hz
        apply max_eq_right
        rw [← hb]
        apply mul_le_mul_of_nonneg_left _ hx.le
        apply Real.exp_le_exp.mpr
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left hz hs.le) _
      _ = _ := by simp [integral_const,ProbabilityTheory.cdf_eq_real,smul_eq_mul,mul_comm]
  have hright : (∫ z in Ioi b,max (x*lognormalSpectralWeight s z) y ∂gaussianReal 0 1)=
      x*(1-ProbabilityTheory.cdf (gaussianReal 0 1) (b-s)) := by
    calc
      _ = ∫ z in Ioi b,x*lognormalSpectralWeight s z ∂gaussianReal 0 1 := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro z hz
        apply max_eq_left
        rw [← hb]
        apply mul_le_mul_of_nonneg_left _ hx.le
        apply Real.exp_le_exp.mpr
        exact sub_le_sub_right (mul_le_mul_of_nonneg_left hz.le hs.le) _
      _ = _ := by rw [integral_const_mul,lognormalSpectralWeight_integral_Ioi]
  rw [hleft,hright]

end Verification
