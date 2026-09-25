import Verification.StudentDisintegration
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal

namespace Verification

noncomputable def studentConditionalKernel (r ν : ℝ) : Kernel ℝ ℝ :=
  (Kernel.const ℝ (volume : Measure ℝ)).withDensity (studentConditionalDensity r ν)

theorem studentConditionalKernel_apply {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (x : ℝ) :
    studentConditionalKernel r ν x=volume.withDensity (studentConditionalDensity r ν x) := by
  rw [studentConditionalKernel,Kernel.withDensity_apply _ (measurable_studentConditionalDensity hr ν hν)]
  rfl

theorem studentConditionalKernel_isMarkov {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) : IsMarkovKernel (studentConditionalKernel r ν) := by
  constructor
  intro x
  rw [studentConditionalKernel_apply hr ν hν x]
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    studentConditionalDensity_integral hr ν hν x]

theorem student_joint_eq_compProd {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) :
    (studentTLaw (bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow=
      (marginal (studentTLaw (bivariateCorrelation r) ν hν) 0) ⊗ₘ studentConditionalKernel r ν := by
  let : IsMarkovKernel (studentConditionalKernel r ν) := studentConditionalKernel_isMarkov hr ν hν
  apply Measure.ext_of_lintegral
  intro f hf
  rw [student_joint_disintegration hr ν hν f hf,Measure.lintegral_compProd hf]
  simp_rw [studentConditionalKernel_apply hr ν hν]

theorem student_joint_rectangle_conditional {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (a b : ℝ) :
    ((studentTLaw (bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow).real
      (Iic a ×ˢ Iic b)=
      ∫ x in Iic a, ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) b
        ∂marginal (studentTLaw (bivariateCorrelation r) ν hν) 0 := by
  let : IsMarkovKernel (studentConditionalKernel r ν) := studentConditionalKernel_isMarkov hr ν hν
  rw [measureReal_def,student_joint_eq_compProd hr ν hν,
    Measure.compProd_apply_prod measurableSet_Iic measurableSet_Iic,
    ← integral_toReal ((studentConditionalKernel r ν).measurable_coe measurableSet_Iic).aemeasurable
      (Filter.Eventually.of_forall fun x => measure_lt_top (studentConditionalKernel r ν x) (Iic b))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [← studentConditionalKernel_apply hr ν hν x,ProbabilityTheory.cdf_eq_real]
    rfl

end Verification
