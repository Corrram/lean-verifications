import Verification.StudentCopulaConditional
import Verification.ScaleMixtureSymmetry
import Verification.ScaleMixtureAbsoluteContinuity
import Verification.GaussianTails
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped ENNReal unitInterval

namespace Verification

theorem symmetricCopula_diagonal_eq_triangle (C : Copula 2) (hC : C.transpose=C)
    (hac : C.toMeasure ≪ volume) (t : I) :
    C.diagonal t=2*C.toMeasure.real {u | u 0≤t ∧ u 1≤u 0} := by
  let A := {u : Fin 2 → I | u 0≤t ∧ u 1≤u 0}
  let B := {u : Fin 2 → I | u 1≤t ∧ u 0≤u 1}
  have hA : MeasurableSet A := (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))
  have hB : MeasurableSet B := (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))
  have he : C.toMeasure.real B=C.toMeasure.real A := by
    have hh := congrArg (fun D : Copula 2 => D.toMeasure.real A) hC
    rw [transpose,toMeasure_reindex,map_measureReal_apply (by fun_prop) hA] at hh
    simpa only [A,B,Set.preimage_ofPred_eq,Function.comp_def,Matrix.cons_val_zero,Matrix.cons_val_one] using hh
  have hz : C.toMeasure (A∩B)=0 := by
    apply measure_mono_null (t := {u : Fin 2 → I | u 0=u 1})
    · intro u hu
      exact le_antisymm hu.2.2 hu.1.2
    · exact hac volume_cube_diagonal
  have hset : Iic ![t,t]=A∪B := by
    ext u
    change (∀ i : Fin 2,u i≤![t,t] i) ↔ (u 0≤t ∧ u 1≤u 0) ∨ (u 1≤t ∧ u 0≤u 1)
    simp only [Fin.forall_fin_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor
    · intro hu
      rcases le_total (u 0) (u 1) with h|h
      · exact Or.inr ⟨hu.2,h⟩
      · exact Or.inl ⟨hu.1,h⟩
    · rintro (h|h)
      · exact ⟨h.1,h.2.trans h.1⟩
      · exact ⟨h.2.trans h.1,h.1⟩
  have hu := measureReal_union_add_inter (μ := C.toMeasure) (s := A) hB
  have hzr : C.toMeasure.real (A∩B)=0 := by rw [measureReal_def,hz,ENNReal.toReal_zero]
  rw [hzr,add_zero,he] at hu
  change C.toMeasure.real (Iic ![t,t])=_
  rw [hset,hu]
  ring

theorem student_joint_triangle_conditional {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (a : ℝ) :
    ((studentTLaw (bivariateCorrelation r) ν hν).toMeasure.map MeasurableEquiv.finTwoArrow).real
      {p : ℝ×ℝ | p.1≤a ∧ p.2≤p.1}=
      ∫ x in Iic a, ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) x
        ∂marginal (studentTLaw (bivariateCorrelation r) ν hν) 0 := by
  let μ := marginal (studentTLaw (bivariateCorrelation r) ν hν) 0
  let K := studentConditionalKernel r ν
  let : IsMarkovKernel K := studentConditionalKernel_isMarkov hr ν hν
  let S := {p : ℝ×ℝ | p.1≤a ∧ p.2≤p.1}
  have hS : MeasurableSet S := (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_fst)
  have hi : Integrable (S.indicator (fun _ => (1:ℝ))) (μ ⊗ₘ K) :=
    (integrable_const _).indicator hS
  rw [student_joint_eq_compProd hr ν hν,← integral_indicator_one hS]
  change (∫ p, S.indicator (fun _ => (1:ℝ)) p ∂μ ⊗ₘ K)=_
  rw [Measure.integral_compProd hi,← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : x≤a
    · rw [indicator_of_mem (show x∈Iic a from hx)]
      have he : (fun y => S.indicator (fun _ => (1:ℝ)) (x,y))=(Iic x).indicator (fun _ => (1:ℝ)) := by
        funext y
        simp only [S,indicator,mem_ofPred_eq,hx,true_and,mem_Iic]
      have hint := integral_indicator_one (μ := K x) (s := Iic x) measurableSet_Iic
      change (∫ y, (Iic x).indicator (fun _ => (1:ℝ)) y ∂K x)=(K x).real (Iic x) at hint
      rw [he,hint,← ProbabilityTheory.cdf_eq_real]
      rw [show K x=volume.withDensity (studentConditionalDensity r ν x) from
        studentConditionalKernel_apply hr ν hν x]
    · simp [S,indicator,hx]

theorem studentBivariate_triangle_conditional {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (a : ℝ) :
    (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).toMeasure.real
      {u | u 0≤cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 0) a ∧ u 1≤u 0}=
      ∫ x in Iic a, ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) x
        ∂marginal (studentTLaw (bivariateCorrelation r) ν hν) 0 := by
  let L := studentTLaw (bivariateCorrelation r) ν hν
  let μ := marginal L 0
  let S := {p : ℝ×ℝ | p.1≤a ∧ p.2≤p.1}
  have hS : MeasurableSet S := (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_le measurable_snd measurable_fst)
  have hm : marginal L 1=marginal L 0 := by
    dsimp only [L]
    rw [student_marginal_density ⟨hr.1.le,hr.2.le⟩ ν hν 1,
      student_marginal_density ⟨hr.1.le,hr.2.le⟩ ν hν 0]
  have hM : (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).toMeasure=
      L.toMeasure.map (marginalTransform L) := by
    unfold studentBivariate studentT gaussianScaleMixture ofContinuousMarginals
    rw [toMeasure_ofMap]
    rfl
  have hA : MeasurableSet {u : Fin 2 → I | u 0≤cdfUnit μ a ∧ u 1≤u 0} :=
    (measurableSet_le (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (by fun_prop) (by fun_prop))
  rw [hM,map_measureReal_apply (measurable_marginalTransform L) hA,
    ← student_joint_triangle_conditional hr ν hν a,
    map_measureReal_apply MeasurableEquiv.finTwoArrow.measurable hS]
  congr 1
  ext p
  change (cdfUnit (marginal L 0) (p 0)≤cdfUnit (marginal L 0) a ∧
    cdfUnit (marginal L 1) (p 1)≤cdfUnit (marginal L 0) (p 0)) ↔ (p 0≤a ∧ p 1≤p 0)
  rw [hm]
  change (ProbabilityTheory.cdf μ (p 0)≤ProbabilityTheory.cdf μ a ∧
    ProbabilityTheory.cdf μ (p 1)≤ProbabilityTheory.cdf μ (p 0)) ↔ _
  have hstrict : StrictMono (ProbabilityTheory.cdf μ) :=
    student_marginal_cdf_strictMono ⟨hr.1.le,hr.2.le⟩ ν hν 0
  exact and_congr hstrict.le_iff_le hstrict.le_iff_le

theorem studentBivariate_diagonal_conditional {r : ℝ} (hr : r∈Ioo (-1) 1)
    (ν : ℝ) (hν : 0<ν) (a : ℝ) :
    (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).diagonal
      (cdfUnit (marginal (studentTLaw (bivariateCorrelation r) ν hν) 0) a)=
      2*∫ x in Iic a, ProbabilityTheory.cdf (volume.withDensity (studentConditionalDensity r ν x)) x
        ∂marginal (studentTLaw (bivariateCorrelation r) ν hν) 0 := by
  have hp : ∀ᵐ t ∂(gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)).toMeasure,
      0<(Real.sqrt t)⁻¹ := by
    filter_upwards [ae_pos_gammaMeasure (ν/2) (ν/2)] with t ht
    exact inv_pos.mpr (Real.sqrt_pos.mpr ht)
  have he := gaussianScaleMixture_transpose ⟨hr.1.le,hr.2.le⟩
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹) (by fun_prop) hp
  have hac := gaussianScaleMixture_absolutelyContinuous hr
    (gammaProbability (ν/2) (ν/2) (by positivity) (by positivity)) (fun t => (Real.sqrt t)⁻¹) (by fun_prop) hp
  change (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).transpose=
    studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν at he
  change (studentBivariate r ⟨hr.1.le,hr.2.le⟩ ν hν).toMeasure ≪ volume at hac
  rw [symmetricCopula_diagonal_eq_triangle _ he hac,studentBivariate_triangle_conditional hr ν hν a]

end Verification
