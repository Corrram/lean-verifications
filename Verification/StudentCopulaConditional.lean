import Verification.StudentConditionalKernel
import Verification.StudentBivariate
import Verification.GaussianConditional

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal unitInterval

namespace Verification

theorem student_marginal_cdf_continuous {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    Continuous (ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation r) ν hν) i)) := by
  exact continuous_gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht)) i

theorem student_marginal_cdf_strictMono {r : ℝ} (hr : r∈Icc (-1) 1)
    (ν : ℝ) (hν : 0<ν) (i : Fin 2) :
    StrictMono (ProbabilityTheory.cdf (marginal (studentTLaw (bivariateCorrelation r) ν hν) i)) := by
  unfold studentTLaw
  rw [gaussianScaleMixtureLaw_marginal _ (bivariateCorrelation_posSemidef hr)
    (by intro j; fin_cases j <;> rfl) _ _ (by fun_prop) i]
  exact normalScaleMixtureMarginal_cdf_strictMono
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹)
    (by fun_prop) (by
      filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
      exact inv_pos.mpr (Real.sqrt_pos.mpr ht))

theorem studentBivariate_cdf_conditional {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (a b : ℝ) :
    (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).cdf
      ![cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 0) a,
        cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 1) b]=
      ∫ x in Iic a, ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) b
        ∂marginal (studentTLaw (bivariateCorrelation r) ν hν) 0 := by
  let L := studentTLaw (bivariateCorrelation r) ν hν
  have hC := studentBivariate_isSklarCopula r ⟨hr.1.le,hr.2.le⟩ ν hν ![a,b]
  have hvec : marginalTransform L ![a,b]=
      ![cdfUnit (marginal L 0) a,cdfUnit (marginal L 1) b] := by
    ext i
    fin_cases i <;> rfl
  change (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).cdf (marginalTransform L ![a,b])=
    L.toMeasure.real (Iic ![a,b]) at hC
  rw [hvec] at hC
  rw [hC,← student_joint_rectangle_conditional hr ν hν a b]
  rw [map_measureReal_apply MeasurableEquiv.finTwoArrow.measurable
    (measurableSet_Iic.prod measurableSet_Iic)]
  congr 1
  ext p
  change (∀ i : Fin 2,p i≤![a,b] i) ↔ (p 0≤a ∧ p 1≤b)
  simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]

theorem measurable_studentConditional_cdf {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (b : ℝ) :
    Measurable (fun x => ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) b) := by
  let : IsMarkovKernel (studentConditionalKernel r ν) := studentConditionalKernel_isMarkov hr ν hν
  have he : (fun x => ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) b)=
      fun x => ((studentConditionalKernel r ν x) (Iic b)).toReal := by
    funext x
    rw [← studentConditionalKernel_apply hr ν hν x,ProbabilityTheory.cdf_eq_real]
    rfl
  rw [he]
  exact ((studentConditionalKernel r ν).measurable_coe measurableSet_Iic).ennreal_toReal

theorem studentBivariate_conditionalCDF {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (b : ℝ) :
    (fun x => (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).conditionalCDF
      (cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 0) x)
      (cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 1) b))
      =ᵐ[marginal (studentTLaw (bivariateCorrelation r) ν hν) 0]
      fun x => ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) b := by
  let μ := marginal (studentTLaw (bivariateCorrelation r) ν hν) 0
  let v := cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 1) b
  let C := studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν
  have hmp := measurePreserving_cdfUnit μ (student_marginal_cdf_continuous ⟨hr.1.le,hr.2.le⟩ ν hν 0)
  have hK := hmp.integrable_comp_of_integrable (C.integrable_conditionalCDF v)
  have hf : Integrable (fun x => ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) b) μ := by
    apply Integrable.of_bound (measurable_studentConditional_cdf hr ν hν b).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (ProbabilityTheory.cdf_nonneg _ _)]
      exact ProbabilityTheory.cdf_le_one _ _
  apply ae_eq_of_nonneg_Iic_integrals hK hf
    (fun x => C.conditionalCDF_nonneg _ _) (fun x => ProbabilityTheory.cdf_nonneg _ _)
  intro a
  have hpre : (cdfUnit μ) ⁻¹' Iic (cdfUnit μ a)=Iic a := by
    ext x
    change ProbabilityTheory.cdf μ x≤ProbabilityTheory.cdf μ a ↔ x≤a
    exact (student_marginal_cdf_strictMono ⟨hr.1.le,hr.2.le⟩ ν hν 0).le_iff_le
  have he := setIntegral_map (μ := μ) (g := cdfUnit μ)
    (f := fun u => C.conditionalCDF u v) (s := Iic (cdfUnit μ a)) measurableSet_Iic
    (C.measurable_conditionalCDF_left _).aestronglyMeasurable hmp.measurable.aemeasurable
  rw [hmp.map_eq,hpre] at he
  dsimp only [Function.comp_def]
  rw [← he,← C.cdf_eq_integral_conditionalCDF]
  exact studentBivariate_cdf_conditional hr ν hν a b

end Verification
