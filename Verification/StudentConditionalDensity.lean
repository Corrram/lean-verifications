import Verification.StudentJointDensity

open ProbabilityTheory MeasureTheory Real Set
open scoped ENNReal

namespace Verification

theorem student_precision_density_update {ν t : ℝ} (hν : 0<ν) (ht : 0<t) (x : ℝ) :
    gammaPDF (ν/2) (ν/2) t*gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x=
      ENNReal.ofReal (studentMarginalPDF ν x)*gammaPDF (ν/2+1/2) (ν/2+x^2/2) t := by
  have hn : gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x=
      ENNReal.ofReal ((Real.sqrt (2*Real.pi))⁻¹)*
        ENNReal.ofReal (t^((1:ℝ)/2)*Real.exp (-((x^2/2)*t))) := by
    rw [gaussianPDF,gaussianPDFReal_inverse_sqrt ht x,← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hn,mul_left_comm,
    gammaPDF_power_exp (by positivity) (by positivity) (by positivity) (by positivity) ht,
    ← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
  rfl

theorem student_precision_measure_update (ν : ℝ) (hν : 0<ν) (x : ℝ) :
    (gammaMeasure (ν/2) (ν/2)).withDensity
      (fun t => gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x)=
      ENNReal.ofReal (studentMarginalPDF ν x) • gammaMeasure (ν/2+1/2) (ν/2+x^2/2) := by
  have hpdf (a b : ℝ) : Measurable (gammaPDF a b) := (measurable_gammaPDFReal a b).ennreal_ofReal
  have hn : Measurable (fun t => gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  have he : (fun t => gammaPDF (ν/2) (ν/2) t*
      gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x)=ᵐ[volume]
      fun t => ENNReal.ofReal (studentMarginalPDF ν x)*gammaPDF (ν/2+1/2) (ν/2+x^2/2) t := by
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with t ht
    rcases lt_or_gt_of_ne ht with hn|hp
    · simp only [gammaPDF_of_neg hn,zero_mul,mul_zero]
    · exact student_precision_density_update hν hp x
  rw [gammaMeasure,← withDensity_mul _ (hpdf _ _) hn]
  change volume.withDensity (fun t => gammaPDF (ν/2) (ν/2) t*
    gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) x)=_
  rw [withDensity_congr_ae he]
  exact withDensity_smul _ (hpdf _ _)

theorem student_joint_density_factorization {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (p : ℝ×ℝ) :
    ENNReal.ofReal (studentJointPDF r ν p)=ENNReal.ofReal (studentMarginalPDF ν p.1)*
      ∫⁻ t, gaussianPDF (r*p.1)
        (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2
          ∂gammaMeasure (ν/2+1/2) (ν/2+p.1^2/2) := by
  rw [← student_joint_density_evaluation hr ν hν p]
  unfold gaussianScaleMixtureJointDensity
  change (∫⁻ t, gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) p.1*
      gaussianPDF (r*p.1) (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2
        ∂gammaMeasure (ν/2) (ν/2))=_
  have hm : Measurable (fun t => gaussianPDF 0 (NNReal.mk ((Real.sqrt t)⁻¹^2) (sq_nonneg _)) p.1) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  have hg : Measurable (fun t => gaussianPDF (r*p.1)
      (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.2) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  have he := lintegral_withDensity_eq_lintegral_mul (gammaMeasure (ν/2) (ν/2)) hm hg
  simp only [Pi.mul_apply] at he
  rw [← he,student_precision_measure_update ν hν p.1,lintegral_smul_measure]
  rfl

noncomputable def studentConditionalDensity (r ν x y : ℝ) : ℝ≥0∞ :=
  ∫⁻ t, gaussianPDF (r*x)
    (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) y
      ∂gammaMeasure (ν/2+1/2) (ν/2+x^2/2)

theorem studentConditionalDensity_integral {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (x : ℝ) :
    (∫⁻ y, studentConditionalDensity r ν x y)=1 := by
  let μ := gammaMeasure (ν/2+1/2) (ν/2+x^2/2)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_gammaMeasure (by positivity) (by positivity)
  have hD : Measurable (fun p : ℝ×ℝ => gaussianPDF (r*x)
      (NNReal.mk (((Real.sqrt p.2)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) p.1) := by
    unfold gaussianPDF gaussianPDFReal
    fun_prop
  change (∫⁻ y, ∫⁻ t, gaussianPDF (r*x)
    (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) y ∂μ)=1
  rw [lintegral_lintegral_swap hD.aemeasurable]
  have he : (fun t => ∫⁻ y, gaussianPDF (r*x)
      (NNReal.mk (((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2) (sq_nonneg _)) y)=ᵐ[μ] fun _ => 1 := by
    filter_upwards [ae_pos_gammaMeasure (ν/2+1/2) (ν/2+x^2/2)] with t ht
    apply lintegral_gaussianPDF_eq_one
    intro hz
    have hz' : ((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2=0 := congrArg (fun v : NNReal => (v:ℝ)) hz
    have hh : 0<1-r^2 := by nlinarith [hr.1,hr.2]
    have hp : 0<((Real.sqrt t)⁻¹*Real.sqrt (1-r^2))^2 := by positivity
    exact hp.ne' hz'
  rw [lintegral_congr_ae he]
  simp

end Verification
