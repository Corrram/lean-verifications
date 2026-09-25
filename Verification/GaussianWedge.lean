import Verification.QuadrantScale
import Verification.ExponentialIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Verification.GaussianReflection

open MeasureTheory Set ProbabilityTheory

namespace Verification

theorem integral_gaussian_radial {b : ℝ} (hb : 0<b) :
    (∫ x in Ioi (0:ℝ), x*Real.exp (-b*x^2))=1/(2*b) := by
  have hh := integral_comp_rpow_Ioi_of_pos (g := fun t : ℝ => Real.exp (-b*t))
    (p := 2) (by norm_num)
  norm_num [smul_eq_mul,Real.rpow_two] at hh
  simp only [← neg_mul] at hh
  have he : (∫ x in Ioi (0:ℝ), 2*x*Real.exp (-b*x^2))=
      2*(∫ x in Ioi (0:ℝ), x*Real.exp (-b*x^2)) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [he,integral_exp_mul_Ioi (neg_neg_of_pos hb) 0] at hh
  simp only [mul_zero,Real.exp_zero] at hh
  have hb0 := hb.ne'
  field_simp at hh ⊢
  simpa only [mul_comm] using hh

theorem integral_gaussian_wedge {a : ℝ} (ha : 0≤a) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      if y≤a*x then Real.exp (-(x^2+y^2)/2) else 0)=Real.arctan a := by
  let f : ℝ × ℝ → ℝ := fun z => if z.2≤a*z.1 then Real.exp (-(z.1^2+z.2^2)/2) else 0
  have hm : Measurable f := by
    exact Measurable.ite (measurableSet_le measurable_snd (measurable_const.mul measurable_fst))
      (by fun_prop) measurable_const
  have hn (z : ℝ × ℝ) : 0≤f z := by dsimp [f]; split_ifs <;> positivity
  have hi : Integrable f ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi 0))) := by
    have hg : IntegrableOn (fun x : ℝ => Real.exp (-(1/2)*x^2)) (Ioi (0:ℝ)) :=
      (integrable_exp_neg_mul_sq (b := 1/2) (by norm_num)).integrableOn
    apply (hg.mul_prod hg).mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hn z)]
      dsimp [f]
      split_ifs
      · apply le_of_eq
        rw [← Real.exp_add]
        congr 1
        ring
      · positivity
  change (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ), f (x,y))=_
  rw [integral_quadrant_scale f hm hn hi]
  have he (s : ℝ) : (∫ x in Ioi (0:ℝ), max 0 x*f (x,x*s))=
      (Iic a).indicator (fun t : ℝ => (1+t^2)⁻¹) s := by
    have hp : 0<(1+s^2)/2 := by positivity
    by_cases hs : s≤a
    · rw [indicator_of_mem (show s∈Iic a from hs)]
      have hg : (∫ x in Ioi (0:ℝ), max 0 x*f (x,x*s))=
          ∫ x in Ioi (0:ℝ), x*Real.exp (-((1+s^2)/2)*x^2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx' : 0<x := hx
        have hxs : x*s≤a*x := by nlinarith
        dsimp only [f]
        rw [max_eq_right hx'.le,ite_eq_left hxs]
        congr 2
        ring
      rw [hg,integral_gaussian_radial hp]
      field_simp
    · rw [indicator_of_notMem (show s∉Iic a from hs)]
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      have hx' : 0<x := hx
      have hxs : ¬x*s≤a*x := by nlinarith
      simp [f,hxs]
  simp_rw [he]
  rw [setIntegral_indicator measurableSet_Iic]
  have hs : Ioi (0:ℝ)∩Iic a=Ioc 0 a := by ext t; simp
  rw [hs,← intervalIntegral.integral_of_le ha,integral_inv_one_add_sq]
  simp

theorem setIntegral_standardGaussian (f : ℝ → ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫ x in s, f x ∂gaussianReal 0 1)=∫ x in s, gaussianPDFReal 0 1 x*f x := by
  rw [← integral_indicator hs,integral_gaussianReal_eq_integral_smul (by norm_num),
    ← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x∈s <;> simp [hx]

theorem standardGaussian_pdf_product (x y : ℝ) :
    gaussianPDFReal 0 1 x*gaussianPDFReal 0 1 y=
      (1/(2*Real.pi))*Real.exp (-(x^2+y^2)/2) := by
  have hs : (Real.sqrt (2*Real.pi))^2=2*Real.pi := Real.sq_sqrt (by positivity)
  have he : Real.exp (-(x^2+y^2)/2)=Real.exp (-x^2/2)*Real.exp (-y^2/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [gaussianPDFReal,NNReal.coe_one,sub_zero,mul_one]
  rw [he]
  calc
    _ = (1/Real.sqrt (2*Real.pi))^2*(Real.exp (-x^2/2)*Real.exp (-y^2/2)) := by ring
    _ = _ := by rw [div_pow,one_pow,hs]

theorem standardGaussian_wedge {a : ℝ} (ha : 0≤a) :
    (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      (if y≤a*x then (1:ℝ) else 0) ∂gaussianReal 0 1 ∂gaussianReal 0 1)=
      Real.arctan a/(2*Real.pi) := by
  simp_rw [setIntegral_standardGaussian _ measurableSet_Ioi]
  have he (x : ℝ) : (∫ y in Ioi (0:ℝ), gaussianPDFReal 0 1 x*
      (gaussianPDFReal 0 1 y*(if y≤a*x then (1:ℝ) else 0)))=
      (1/(2*Real.pi))*(∫ y in Ioi (0:ℝ), if y≤a*x then Real.exp (-(x^2+y^2)/2) else 0) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y _
    dsimp only
    split_ifs <;> simp only [mul_one,mul_zero]
    exact standardGaussian_pdf_product x y
  simp_rw [← integral_const_mul,he]
  rw [integral_const_mul,integral_gaussian_wedge ha]
  ring

theorem standardGaussian_cdf_zero : ProbabilityTheory.cdf (gaussianReal 0 1) 0=1/2 := by
  have hh := standardNormalCDF_neg 0
  rw [neg_zero] at hh
  linarith

theorem standardGaussian_cdf_nonneg {b : ℝ} (hb : 0≤b) :
    ProbabilityTheory.cdf (gaussianReal 0 1) b =
      1/2+(∫ y in Ioi (0:ℝ), if y≤b then (1:ℝ) else 0 ∂gaussianReal 0 1) := by
  let μ := gaussianReal 0 1
  have hi : Integrable (fun y : ℝ => if y≤b then (1:ℝ) else 0) μ := by
    apply (integrable_const (1:ℝ)).mono'
      ((Measurable.ite measurableSet_Iic measurable_const measurable_const).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun y => by split_ifs <;> norm_num
  have hh := integral_add_compl (s := Iic (0:ℝ)) measurableSet_Iic hi
  rw [compl_Iic] at hh
  have he : (∫ y in Iic (0:ℝ), (if y≤b then (1:ℝ) else 0) ∂μ)=1/2 := by
    have hfun : (∫ y in Iic (0:ℝ), (if y≤b then (1:ℝ) else 0) ∂μ)=
        ∫ _ in Iic (0:ℝ), (1:ℝ) ∂μ := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro y hy
      exact ite_eq_left (le_trans hy hb)
    rw [hfun,integral_const]
    simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one]
    change μ.real (Iic 0)=1/2
    rw [← ProbabilityTheory.cdf_eq_real,standardGaussian_cdf_zero]
  have he' : (∫ y, (if y≤b then (1:ℝ) else 0) ∂μ)=ProbabilityTheory.cdf μ b := by
    rw [ProbabilityTheory.cdf_eq_real]
    simpa only [indicator,mem_Iic,Pi.one_apply] using integral_indicator_one (μ := μ) measurableSet_Iic
  rw [he,he'] at hh
  exact hh.symm

theorem integral_standardGaussian_cdf_nonneg {a : ℝ} (ha : 0≤a) :
    (∫ x in Ioi (0:ℝ), ProbabilityTheory.cdf (gaussianReal 0 1) (a*x) ∂gaussianReal 0 1)=
      1/4+Real.arctan a/(2*Real.pi) := by
  let μ := gaussianReal 0 1
  have hi : Integrable (fun x => ProbabilityTheory.cdf μ (a*x)) (μ.restrict (Ioi 0)) := by
    apply (integrable_const (1:ℝ)).mono'
      (((monotone_cdf μ).measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Function.comp_def,Pi.mul_apply,id_eq]
      rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg μ _)]
      exact cdf_le_one μ _
  have hm : μ.real (Ioi (0:ℝ))=1/2 := by
    rw [← compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ,
      ← ProbabilityTheory.cdf_eq_real,standardGaussian_cdf_zero]
    norm_num
  have he : (∫ x in Ioi (0:ℝ), ∫ y in Ioi (0:ℝ),
      (if y≤a*x then (1:ℝ) else 0) ∂μ ∂μ)=
      (∫ x in Ioi (0:ℝ), ProbabilityTheory.cdf μ (a*x) ∂μ)-1/4 := by
    calc
      _ = ∫ x in Ioi (0:ℝ), (ProbabilityTheory.cdf μ (a*x)-1/2) ∂μ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hh := standardGaussian_cdf_nonneg (mul_nonneg ha (le_of_lt hx))
        linarith
      _ = _ := by
        rw [integral_sub hi (integrable_const _),integral_const]
        simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul]
        change _-μ.real (Ioi 0)*(1/2)=_
        rw [hm]
        ring
  rw [standardGaussian_wedge ha] at he
  linarith

theorem integral_standardGaussian_cdf (a : ℝ) :
    (∫ x in Ioi (0:ℝ), ProbabilityTheory.cdf (gaussianReal 0 1) (a*x) ∂gaussianReal 0 1)=
      1/4+Real.arctan a/(2*Real.pi) := by
  by_cases ha : 0≤a
  · exact integral_standardGaussian_cdf_nonneg ha
  let μ := gaussianReal 0 1
  have hi : Integrable (fun x => ProbabilityTheory.cdf μ ((-a)*x)) (μ.restrict (Ioi 0)) := by
    apply (integrable_const (1:ℝ)).mono'
      (((monotone_cdf μ).measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun x => by
      dsimp only [Function.comp_def,Pi.mul_apply,id_eq]
      rw [Real.norm_eq_abs,abs_of_nonneg (cdf_nonneg μ _)]
      exact cdf_le_one μ _
  have hm : μ.real (Ioi (0:ℝ))=1/2 := by
    rw [← compl_Iic,measureReal_compl measurableSet_Iic,probReal_univ,
      ← ProbabilityTheory.cdf_eq_real,standardGaussian_cdf_zero]
    norm_num
  have he (x : ℝ) : ProbabilityTheory.cdf μ (a*x)=1-ProbabilityTheory.cdf μ ((-a)*x) := by
    simpa only [neg_mul,neg_neg] using standardNormalCDF_neg ((-a)*x)
  change (∫ x in Ioi (0:ℝ), ProbabilityTheory.cdf μ (a*x) ∂μ)=_
  simp_rw [he]
  rw [integral_sub (integrable_const _) hi,integral_const]
  simp only [measureReal_restrict_apply_univ,smul_eq_mul,mul_one,hm]
  rw [integral_standardGaussian_cdf_nonneg (show 0≤ -a by linarith),Real.arctan_neg]
  ring

end Verification
