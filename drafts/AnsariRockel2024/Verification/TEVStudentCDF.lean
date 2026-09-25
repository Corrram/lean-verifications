import Verification.GaussianPowerIntegral
import Verification.GaussianWedge
import Verification.ScaleMixtureCDF
import Copula.Families.StudentT

/-! # Student-t CDF as a gamma mixture and the chi-type substitution

`studentTCDF k x` is the CDF at `x` of the standard Student-t law with `k>0` degrees of
freedom, written as the normal scale mixture with gamma precision of shape and rate `k/2`.
The main result identifies the positive Gaussian power moment weighted by a normal CDF
with a Student-t CDF with `ν+1` degrees of freedom. This is the analytic step behind the
t-EV Pickands function.
-/

open ProbabilityTheory MeasureTheory Real Set

namespace Verification

/-- Standard Student-t CDF with `k` degrees of freedom, as a gamma-precision normal mixture. -/
noncomputable def studentTCDF (k x : ℝ) : ℝ :=
  ∫ t, ProbabilityTheory.cdf (gaussianReal 0 1) (x*Real.sqrt t) ∂gammaMeasure (k/2) (k/2)

theorem studentTCDF_eq_mixture_cdf (k : ℝ) (hk : 0<k) (x : ℝ) :
    studentTCDF k x=ProbabilityTheory.cdf (normalScaleMixtureMarginal
      (gammaProbability (k/2) (k/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)) x := by
  rw [normalScaleMixtureMarginal_cdf _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (k/2) (k/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))]
  simp only [div_inv_eq_mul]
  rfl

theorem studentTCDF_strictMono (k : ℝ) (hk : 0<k) : StrictMono (studentTCDF k) := by
  intro a b hab
  rw [studentTCDF_eq_mixture_cdf k hk,studentTCDF_eq_mixture_cdf k hk]
  exact normalScaleMixtureMarginal_cdf_strictMono _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (k/2) (k/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) hab

theorem studentTCDF_zero (k : ℝ) (hk : 0<k) : studentTCDF k 0=1/2 := by
  have : IsProbabilityMeasure (gammaMeasure (k/2) (k/2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  simp [studentTCDF,standardGaussian_cdf_zero]

theorem studentTCDF_neg (k : ℝ) (hk : 0<k) (x : ℝ) :
    studentTCDF k (-x)=1-studentTCDF k x := by
  rw [studentTCDF_eq_mixture_cdf k hk,studentTCDF_eq_mixture_cdf k hk]
  exact normalScaleMixtureMarginal_cdf_neg _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (k/2) (k/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) x

theorem studentTCDF_nonneg (k x : ℝ) : 0≤studentTCDF k x :=
  integral_nonneg fun _ => ProbabilityTheory.cdf_nonneg _ _

theorem studentTCDF_le_one (k : ℝ) (hk : 0<k) (x : ℝ) : studentTCDF k x≤1 := by
  have : IsProbabilityMeasure (gammaMeasure (k/2) (k/2)) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  calc
    studentTCDF k x≤∫ _t, (1:ℝ) ∂gammaMeasure (k/2) (k/2) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => ProbabilityTheory.cdf_nonneg _ _)
        (integrable_const _) (Filter.Eventually.of_forall fun _ => ProbabilityTheory.cdf_le_one _ _)
    _ = 1 := by simp

/-- Gamma integrals of bounded functions as Lebesgue integrals over the positive half-line. -/
theorem integral_gammaMeasure_Ioi {a b : ℝ} (ha : 0<a) (hb : 0<b) (f : ℝ → ℝ) :
    (∫ t, f t ∂gammaMeasure a b)=∫ t in Ioi 0, gammaPDFReal a b t*f t := by
  rw [gammaMeasure,integral_withDensity_eq_integral_toReal_smul
    (by unfold gammaPDF; fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [gammaPDF,ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hb _),smul_eq_mul]
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [(Measure.ae_ne volume (0:ℝ))] with t ht
  by_cases hp : 0<t
  · simp [indicator_of_mem (show t∈Ioi (0:ℝ) from hp)]
  · have hn : t<0 := lt_of_le_of_ne (le_of_not_gt hp) ht
    rw [indicator_of_notMem (show t∉Ioi (0:ℝ) from hp)]
    simp [gammaPDFReal,not_le.mpr hn]

/-- The chi-type substitution `t=z²/(ν+1)` on the positive half-line. -/
theorem integral_Ioi_rpow_gaussian_subst (ν : ℝ) (hν : 0<ν) (g : ℝ → ℝ) :
    (∫ z in Ioi 0, z^ν*Real.exp (-(z^2/2))*g z)=
      (ν+1)^((ν+1)/2)/2*∫ t in Ioi 0, t^((ν-1)/2)*Real.exp (-((ν+1)/2*t))*
        g (Real.sqrt ((ν+1)*t)) := by
  set c : ℝ := Real.sqrt (ν+1) with hc
  have hcp : 0<c := Real.sqrt_pos.mpr (by linarith)
  have hc2 : c^2=ν+1 := Real.sq_sqrt (by linarith)
  let h : ℝ → ℝ := fun t => t^((ν-1)/2)*Real.exp (-((ν+1)/2*t))*g (Real.sqrt ((ν+1)*t))
  have hsub := integral_comp_rpow_Ioi_of_pos (g := h) (by norm_num : (0:ℝ)<2)
  let F : ℝ → ℝ := fun y => 2*(y/c)^ν*Real.exp (-(y^2/2))*g y
  have hF : (∫ x in Ioi (0:ℝ), ((2:ℝ)*x^((2:ℝ)-1)) • h (x^(2:ℝ)))=∫ x in Ioi (0:ℝ), F (c*x) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0<x := hx
    simp only [h,F,smul_eq_mul]
    have hpow : (x^(2:ℝ))^((ν-1)/2)=x^(ν-1) := by
      rw [← Real.rpow_mul hx0.le]
      congr 1
      ring
    have hmul : x*x^(ν-1)=x^ν := by
      nth_rw 1 [← Real.rpow_one x]
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    have hsq : Real.sqrt ((ν+1)*x^(2:ℝ))=c*x := by
      rw [Real.rpow_two,Real.sqrt_mul (by linarith),Real.sqrt_sq hx0.le]
    have hdiv : c*x/c=x := by field_simp
    rw [hpow,hsq,hdiv,show (2:ℝ)-1=1 by norm_num,Real.rpow_one,Real.rpow_two]
    have he : (ν+1)/2*x^2=(c*x)^2/2 := by rw [mul_pow,hc2]; ring
    rw [he]
    calc
      2*x*(x^(ν-1)*Real.exp (-((c*x)^2/2))*g (c*x))=
          2*(x*x^(ν-1))*Real.exp (-((c*x)^2/2))*g (c*x) := by ring
      _ = _ := by rw [hmul]
  rw [hF,integral_comp_mul_left_Ioi F 0 hcp,mul_zero] at hsub
  have hF2 : (∫ y in Ioi (0:ℝ), F y)=2*(c^ν)⁻¹*∫ z in Ioi 0, z^ν*Real.exp (-(z^2/2))*g z := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    have hy0 : 0<y := hy
    simp only [F]
    rw [Real.div_rpow hy0.le hcp.le]
    field_simp
  rw [hF2,smul_eq_mul] at hsub
  have hcν : 0<c^ν := Real.rpow_pos_of_pos hcp ν
  have hpow : c^(ν+1)=(ν+1)^((ν+1)/2) := by
    rw [hc,Real.sqrt_eq_rpow,← Real.rpow_mul (by linarith)]
    congr 1
    ring
  have hcc : c^(ν+1)=c*c^ν := by
    rw [Real.rpow_add hcp,Real.rpow_one,mul_comm]
  rw [← hpow,hcc]
  have hinv : c⁻¹*(2*(c^ν)⁻¹*∫ z in Ioi 0, z^ν*Real.exp (-(z^2/2))*g z)=∫ t in Ioi 0, h t := hsub
  field_simp at hinv ⊢
  linarith [hinv]

/-- The positive Gaussian power moment weighted by a normal CDF is a Student-t CDF with
`ν+1` degrees of freedom. -/
theorem positivePower_normalCDF_integral (ν : ℝ) (hν : 0<ν) (β : ℝ) :
    (∫ z, positivePower ν z*ProbabilityTheory.cdf (gaussianReal 0 1) (β*z) ∂gaussianReal 0 1)=
      gaussianPositiveMoment ν*studentTCDF (ν+1) (β*Real.sqrt (ν+1)) := by
  set Φ := ProbabilityTheory.cdf (gaussianReal 0 1)
  -- left side as a Lebesgue integral over the positive half-line
  have hL : (∫ z, positivePower ν z*Φ (β*z) ∂gaussianReal 0 1)=
      (Real.sqrt (2*Real.pi))⁻¹*∫ z in Ioi 0, z^ν*Real.exp (-(z^2/2))*Φ (β*z) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0:ℝ)) (fun z hz => by
      have hz' : z≤0 := le_of_not_gt hz
      simp only [positivePower,max_eq_right hz',Real.zero_rpow hν.ne',zero_mul])]
    rw [setIntegral_standardGaussian _ measurableSet_Ioi,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    have hzpos : (0:ℝ)<z := hz
    simp only [positivePower,max_eq_left hzpos.le,gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero]
    rw [show -(z^2)/(2:ℝ)=-(z^2/2) by ring]
    ring
  set A : ℝ := (ν+1)/2 with hA
  have hApos : 0<A := by positivity
  have hR : studentTCDF (ν+1) (β*Real.sqrt (ν+1))=
      A^A/Real.Gamma A*∫ t in Ioi 0, t^((ν-1)/2)*Real.exp (-((ν+1)/2*t))*
        Φ (β*Real.sqrt ((ν+1)*t)) := by
    unfold studentTCDF
    rw [integral_gammaMeasure_Ioi hApos hApos,← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ)<t := ht
    simp only [gammaPDFReal,if_pos ht0.le]
    rw [show A-1=(ν-1)/2 by rw [hA]; ring,Real.sqrt_mul (by linarith) t]
    ring_nf
  rw [hL,integral_Ioi_rpow_gaussian_subst ν hν,hR,gaussianPositiveMoment_formula ν hν]
  have hG : 0<Real.Gamma A := Real.Gamma_pos_of_pos hApos
  have h2A : (2:ℝ)^A*A^A=(ν+1)^A := by
    rw [← Real.mul_rpow (by norm_num) hApos.le,hA]
    congr 1
    ring
  rw [← hA]
  field_simp
  rw [← h2A]
  ring

end Verification
