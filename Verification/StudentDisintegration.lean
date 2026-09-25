import Verification.StudentConditionalCDF

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal

namespace Verification

theorem measurable_studentConditionalDensity {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    Measurable (fun p : ℝ×ℝ => studentConditionalDensity r ν p.1 p.2) := by
  have he : (fun p : ℝ×ℝ => studentConditionalDensity r ν p.1 p.2)=
      fun p => (ENNReal.ofReal (studentMarginalPDF ν p.1))⁻¹*ENNReal.ofReal (studentJointPDF r ν p) := by
    funext p
    rw [student_joint_density_factorization hr ν hν p,← mul_assoc,
      ENNReal.inv_mul_cancel (by exact (ENNReal.ofReal_pos.mpr (studentMarginalPDF_pos hν p.1)).ne')
        ENNReal.ofReal_ne_top,one_mul]
    rfl
  rw [he]
  unfold studentMarginalPDF studentJointPDF studentQuadratic
  fun_prop

theorem student_marginal_density {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    marginal (studentTLaw (bivariateCorrelation r) ν hν) i=
      volume.withDensity (fun x => ENNReal.ofReal (studentMarginalPDF ν x)) := by
  unfold studentTLaw
  rw [gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) i]
  change normalScaleMixtureMarginal
      (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity))
      (fun t => (Real.sqrt t)⁻¹)=_
  rw [normalScaleMixtureMarginal_withDensity _ _ (by fun_prop) (by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht))]
  congr 1
  funext x
  exact student_marginal_density_evaluation ν hν x

theorem student_joint_disintegration {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (f : ℝ×ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂(studentTLaw (bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow)=
      ∫⁻ x, ∫⁻ y, f (x,y) ∂volume.withDensity (studentConditionalDensity r ν x)
        ∂marginal (studentTLaw (bivariateCorrelation r) ν hν) 0 := by
  have hD := measurable_studentConditionalDensity hr ν hν
  have hM : Measurable (fun x => ENNReal.ofReal (studentMarginalPDF ν x)) := by
    unfold studentMarginalPDF
    fun_prop
  have hJ : (studentTLaw (bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow=
      volume.withDensity (fun p : ℝ×ℝ => ENNReal.ofReal (studentMarginalPDF ν p.1)*
        studentConditionalDensity r ν p.1 p.2) := by
    rw [show (studentTLaw (bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow=
      volume.withDensity (gaussianScaleMixtureJointDensity r
        (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)) from
      gaussianScaleMixtureLaw_joint_withDensity hr _ _ (by fun_prop) (by
        filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
        exact inv_pos.mpr (Real.sqrt_pos.mpr ht))]
    congr 1
    funext p
    rw [student_joint_density_evaluation hr ν hν p,student_joint_density_factorization hr ν hν p]
    rfl
  have hm : Measurable (fun p : ℝ×ℝ => ENNReal.ofReal (studentMarginalPDF ν p.1)*
      studentConditionalDensity r ν p.1 p.2) := (hM.comp measurable_fst).mul hD
  have hi : Measurable (fun x => ∫⁻ y, studentConditionalDensity r ν x y*f (x,y)) :=
    (hD.mul hf).lintegral_prod_right
  rw [hJ,lintegral_withDensity_eq_lintegral_mul _ hm hf]
  simp only [Pi.mul_apply]
  have hmf : Measurable (fun p : ℝ×ℝ => ENNReal.ofReal (studentMarginalPDF ν p.1)*
      studentConditionalDensity r ν p.1 p.2*f p) := hm.mul hf
  rw [show (volume : Measure (ℝ×ℝ))=(volume : Measure ℝ).prod volume from rfl,
    lintegral_prod _ hmf.aemeasurable]
  have he : (fun x => ∫⁻ y, ENNReal.ofReal (studentMarginalPDF ν x)*
      studentConditionalDensity r ν x y*f (x,y))=
      fun x => ENNReal.ofReal (studentMarginalPDF ν x)*
        ∫⁻ y, studentConditionalDensity r ν x y*f (x,y) := by
    funext x
    simp only [mul_assoc]
    have hpair : Measurable (fun y : ℝ => (x,y)) := measurable_const.prodMk measurable_id
    have hx := (hD.mul hf).comp hpair
    dsimp only [Function.comp_def,Pi.mul_apply] at hx
    exact lintegral_const_mul _ hx
  dsimp only
  have hwd := lintegral_withDensity_eq_lintegral_mul volume hM hi
  simp only [Pi.mul_apply] at hwd
  rw [he,← hwd,
    ← student_marginal_density ⟨hr.1.le,hr.2.le⟩ ν hν 0]
  apply lintegral_congr
  intro x
  symm
  have hpair : Measurable (fun y : ℝ => (x,y)) := measurable_const.prodMk measurable_id
  have hx := hD.comp hpair
  have hfx := hf.comp hpair
  dsimp only [Function.comp_def] at hx hfx
  exact lintegral_withDensity_eq_lintegral_mul _ hx hfx

end Verification
