import Verification.QuadraticBandContinuity

/-! # Concordance ordering of normalized quadratic-band copulas -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- A larger slope moves conditional mass toward the left in every section. -/
theorem quadraticBand_cdf_mono (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hbd : b ≤ d) (u v : I) :
    (quadraticBand b hb).cdf ![u,v] ≤ (quadraticBand d hd).cdf ![u,v] := by
  let a := quadraticIntercept b hb v
  let c := quadraticIntercept d hd v
  have hp (s t : I) (hst : s ≤ t) : (1-(t : ℝ))^2 ≤ (1-(s : ℝ))^2 := by
    nlinarith [s.property.2,t.property.2,show (s : ℝ) ≤ t from hst]
  have clamp_mono {x y : ℝ} (hxy : x ≤ y) : unitClamp x ≤ unitClamp y :=
    min_le_min le_rfl (max_le_max le_rfl hxy)
  by_cases h : a+b*(1-(u : ℝ))^2 ≤ c+d*(1-(u : ℝ))^2
  · simp only [quadraticBand_cdf]
    apply setIntegral_mono_on (quadraticKernel_integrable b hb v).integrableOn
      (quadraticKernel_integrable d hd v).integrableOn measurableSet_Iic
    intro t ht
    apply clamp_mono
    have hh := mul_nonneg (sub_nonneg.mpr hbd) (sub_nonneg.mpr (hp t u ht))
    dsimp [a,c] at h
    nlinarith only [h,hh]
  · have ht : (∫ t in Ioc u (1:I), quadraticKernel d hd v t) ≤
        ∫ t in Ioc u (1:I), quadraticKernel b hb v t := by
      apply setIntegral_mono_on (quadraticKernel_integrable d hd v).integrableOn
        (quadraticKernel_integrable b hb v).integrableOn measurableSet_Ioc
      intro t ht
      apply clamp_mono
      have hh := mul_nonneg (sub_nonneg.mpr hbd) (sub_nonneg.mpr (hp u t ht.1.le))
      dsimp [a,c] at h
      nlinarith only [h,hh]
    have eb := Copula.integral_Iic_add_Ioc_unit (quadraticKernel_integrable b hb v)
      (show u ≤ (1:I) from u.property.2)
    have ed := Copula.integral_Iic_add_Ioc_unit (quadraticKernel_integrable d hd v)
      (show u ≤ (1:I) from u.property.2)
    have hs : Iic (1:I) = univ := by ext t; simp [unitInterval.le_one']
    rw [hs,Measure.restrict_univ] at eb ed
    have mb : (∫ t, quadraticKernel b hb v t) = (v:ℝ) := quadraticIntercept_mean b hb v
    have md : (∫ t, quadraticKernel d hd v t) = (v:ℝ) := quadraticIntercept_mean d hd v
    rw [mb] at eb
    rw [md] at ed
    rw [quadraticBand_cdf,quadraticBand_cdf]
    change (∫ t in Iic u, quadraticKernel b hb v t) ≤ ∫ t in Iic u, quadraticKernel d hd v t
    linarith

/-- Uniform dependence on the nonnegative slope, including independence. -/
theorem quadraticBand_cdf_abs_sub_le (b d : ℝ) (hb : 0 ≤ b) (hd : 0 ≤ d) (u v : I) :
    |(quadraticBand b hb).cdf ![u,v] - (quadraticBand d hd).cdf ![u,v]| ≤ 2*|b-d| := by
  rw [quadraticBand_cdf,quadraticBand_cdf]
  change |(∫ t in Iic u, quadraticKernel b hb v t) -
    (∫ t in Iic u, quadraticKernel d hd v t)| ≤ _
  rw [← integral_sub (quadraticKernel_integrable b hb v).integrableOn
    (quadraticKernel_integrable d hd v).integrableOn]
  apply abs_integral_le_integral_abs.trans
  calc
    _ ≤ ∫ _t in Iic u, 2*|b-d| := by
      apply setIntegral_mono_on
        ((quadraticKernel_integrable b hb v).sub (quadraticKernel_integrable d hd v)).abs.integrableOn
        (integrable_const _).integrableOn measurableSet_Iic
      intro t _
      exact quadraticKernel_abs_sub_le b d hb hd v t
    _ = (u:ℝ)*(2*|b-d|) := by simp [Measure.real,unitInterval.volume_Iic,u.property.1]
    _ ≤ 2*|b-d| := mul_le_of_le_one_left (by positivity) u.property.2

end Verification
