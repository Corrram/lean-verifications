import Verification.StudentJointDensity

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal

namespace Verification

theorem laplace_gaussian_density_product {r t : ℝ} (hr : r∈Ioo (-1) 1)
    (ht : 0<t) (p : ℝ×ℝ) :
    gaussianPDF 0 (NNReal.mk ((Real.sqrt t)^2) (sq_nonneg _)) p.1*
      gaussianPDF (r*p.1) (NNReal.mk ((Real.sqrt t*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2=
    ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*
      ENNReal.ofReal (t⁻¹*Real.exp (-(studentQuadratic r p/(2*t)))) := by
  have h := student_gaussian_density_product hr (inv_pos.mpr ht) p
  simpa only [Real.sqrt_inv,inv_inv,Real.rpow_one,div_mul_eq_div_mul_one_div,one_div] using h

/-- The radial integral of the bivariate Laplace mixture. Its value may be infinite. -/
noncomputable def laplaceRadialDensity (q : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t⁻¹*Real.exp (-t-q/(2*t)))

theorem laplace_joint_density_evaluation {r : ℝ} (hr : r∈Ioo (-1) 1) (p : ℝ×ℝ) :
    gaussianScaleMixtureJointDensity r (gammaProbability 1 1 zero_lt_one zero_lt_one)
      Real.sqrt p=
    ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*
      laplaceRadialDensity (studentQuadratic r p) := by
  unfold gaussianScaleMixtureJointDensity
  change (∫⁻ t, _ ∂gammaMeasure 1 1)=_
  rw [lintegral_congr_ae (show
    (fun t => gaussianPDF 0 (NNReal.mk ((Real.sqrt t)^2) (sq_nonneg _)) p.1*
      gaussianPDF (r*p.1) (NNReal.mk ((Real.sqrt t*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2)=ᵐ[gammaMeasure 1 1]
    fun t => ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*
      ENNReal.ofReal (t⁻¹*Real.exp (-(studentQuadratic r p/(2*t)))) from by
        filter_upwards [ae_pos_gammaMeasure 1 1] with t ht
        exact laplace_gaussian_density_product hr ht p),
    lintegral_const_mul _ (by fun_prop)]
  congr 1
  have hpdf : Measurable (gammaPDF 1 1) := (measurable_gammaPDFReal 1 1).ennreal_ofReal
  rw [gammaMeasure,lintegral_withDensity_eq_lintegral_mul _ hpdf (by fun_prop)]
  simp only [Pi.mul_apply]
  rw [laplaceRadialDensity,← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with t ht
  rcases lt_or_gt_of_ne ht with hn|hp
  · rw [gammaPDF_of_neg hn,zero_mul,Set.indicator_of_notMem (show t∉Ioi (0:ℝ) from not_lt.mpr hn.le)]
  · rw [Set.indicator_of_mem (show t∈Ioi (0:ℝ) from hp),gammaPDF_of_nonneg hp.le]
    simp only [one_rpow,Real.Gamma_one,div_one,sub_self,Real.rpow_zero,one_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,sub_eq_add_neg,Real.exp_add]
    congr 1
    ring

theorem laplaceRadialDensity_antitone : Antitone laplaceRadialDensity := by
  intro q v hqv
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0<t at ht
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt ht))
  apply Real.exp_le_exp.mpr
  have h := div_le_div_of_nonneg_right hqv (show 0≤2*t by positivity)
  linarith

theorem laplace_joint_radial_withDensity {r : ℝ} (hr : r∈Ioo (-1) 1) :
    (gaussianScaleMixtureLaw (bivariateCorrelation r)
      (gammaProbability 1 1 zero_lt_one zero_lt_one) Real.sqrt).toMeasure.map
        MeasurableEquiv.finTwoArrow=
    (volume : Measure (ℝ×ℝ)).withDensity (fun p =>
      ENNReal.ofReal ((2*Real.pi*Real.sqrt (1-r^2))⁻¹)*
        laplaceRadialDensity (studentQuadratic r p)) := by
  rw [gaussianScaleMixtureLaw_joint_withDensity hr _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure 1 1] with t ht
    exact Real.sqrt_pos.mpr ht)]
  congr 1
  funext p
  exact laplace_joint_density_evaluation hr p

end Verification
