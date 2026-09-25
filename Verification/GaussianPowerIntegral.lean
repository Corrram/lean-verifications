import Verification.GaussianPositivePower
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open ProbabilityTheory MeasureTheory Real Set

namespace Verification

theorem gaussian_rpow_integral (ν b : ℝ) (hν : -1<ν) (hb : 0<b) :
    (∫ z : ℝ in Ioi 0,z^ν*Real.exp (-(b*z^2)))=
      ((1/b)^((ν+1)/2)*Real.Gamma ((ν+1)/2))/2 := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun t : ℝ => t^((ν+1)/2-1)*Real.exp (-(b*t))) (by norm_num : (0:ℝ)<2)
  have he : (∫ z : ℝ in Ioi 0,(2*z^((2:ℝ)-1)) •
      ((z^(2:ℝ))^((ν+1)/2-1)*Real.exp (-(b*(z^(2:ℝ))))))=
      2*(∫ z : ℝ in Ioi 0,z^ν*Real.exp (-(b*z^2))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    simp only [smul_eq_mul,show (2:ℝ)-1=1 by norm_num,Real.rpow_one]
    rw [← Real.rpow_mul hz.le,show (2:ℝ)*((ν+1)/2-1)=ν-1 by ring]
    have hp : z*z^(ν-1)=z^ν := by
      nth_rw 1 [← Real.rpow_one z]
      rw [← Real.rpow_add hz]
      congr 1
      ring
    rw [Real.rpow_two]
    calc
      2*z*(z^(ν-1)*Real.exp (-(b*z^2)))=2*(z*z^(ν-1))*Real.exp (-(b*z^2)) := by ring
      _ = _ := by rw [hp]; ring
  rw [he,Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0<(ν+1)/2) hb] at h
  linarith

theorem gaussianPositiveMoment_formula (ν : ℝ) (hν : 0<ν) :
    gaussianPositiveMoment ν=(Real.sqrt (2*Real.pi))⁻¹*
      ((2:ℝ)^((ν+1)/2)*Real.Gamma ((ν+1)/2)/2) := by
  unfold gaussianPositiveMoment
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ)) (fun z hz => by
    have hz' : z≤0 := le_of_not_gt hz
    simp only [positivePower,max_eq_right hz',Real.zero_rpow hν.ne'])]
  rw [setIntegral_standardGaussian _ measurableSet_Ioi]
  have he : (∫ z in Ioi (0:ℝ),gaussianPDFReal 0 1 z*positivePower ν z)=
      (Real.sqrt (2*Real.pi))⁻¹*(∫ z : ℝ in Ioi 0,z^ν*Real.exp (-((1/2)*z^2))) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    have hzpos : (0:ℝ)<z := hz
    simp only [positivePower,max_eq_left hzpos.le,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,one_div]
    rw [show -(z^2)/(2:ℝ)=-((1/2)*z^2) by ring]
    ring_nf
  rw [he,gaussian_rpow_integral ν (1/2) (by linarith) (by norm_num)]
  norm_num

theorem gaussianPositiveMoment_add_two (ν : ℝ) (hν : 0<ν) :
    gaussianPositiveMoment (ν+2)=(ν+1)*gaussianPositiveMoment ν := by
  rw [gaussianPositiveMoment_formula (ν+2) (by linarith),gaussianPositiveMoment_formula ν hν,
    show (ν+2+1)/2=(ν+1)/2+1 by ring,Real.rpow_add_one (by norm_num : (2:ℝ)≠0),
    Real.Gamma_add_one (by linarith : (ν+1)/2≠0)]
  ring

end Verification
