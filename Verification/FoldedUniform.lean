import Verification.ConditionalCopulaAE
import Verification.BandSampling
import Verification.RampIntegrals

/-! # The copula of (abs(2U-1), U) -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def foldLower (u : I) : I := ⟨(1-(u : ℝ))/2,by constructor <;> linarith [u.property.1,u.property.2]⟩
noncomputable def foldUpper (u : I) : I := ⟨(1+(u : ℝ))/2,by constructor <;> linarith [u.property.1,u.property.2]⟩

@[fun_prop] theorem continuous_foldLower : Continuous foldLower := by unfold foldLower; fun_prop
@[fun_prop] theorem continuous_foldUpper : Continuous foldUpper := by unfold foldUpper; fun_prop

noncomputable def foldKernel (v u : I) : ℝ :=
  (if foldLower u ≤ v then 1 else 0)/2+(if foldUpper u ≤ v then 1 else 0)/2

theorem foldKernel_measurable : Measurable (fun p : I × I => foldKernel p.1 p.2) := by
  unfold foldKernel
  exact ((measurable_const.ite (measurableSet_le (by fun_prop) measurable_fst) measurable_const).div_const 2).add
    ((measurable_const.ite (measurableSet_le (by fun_prop) measurable_fst) measurable_const).div_const 2)

theorem foldKernel_mem (v u : I) : foldKernel v u ∈ Icc (0 : ℝ) 1 := by
  unfold foldKernel
  split_ifs <;> norm_num

theorem foldKernel_integrable (v : I) : Integrable (foldKernel v) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((foldKernel_measurable.comp (by fun_prop : Measurable (fun u : I => (v,u)))).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (foldKernel_mem v u).1]
    exact (foldKernel_mem v u).2

theorem fold_indicator_integrable (f : I → I) (hf : Measurable f) (v : I) :
    Integrable (fun u : I => if f u ≤ v then (1 : ℝ) else 0) := by
  refine (integrable_const (1 : ℝ)).mono'
    ((measurable_const.ite (measurableSet_le hf measurable_const) measurable_const).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun u => by split_ifs <;> norm_num

theorem fold_lower_integral (v : I) :
    (∫ u : I, if foldLower u ≤ v then (1 : ℝ) else 0) = unitClamp (2*(v : ℝ)) := by
  have he (u : I) : foldLower u ≤ v ↔ (unitInterval.symm u : ℝ) ≤ 2*(v : ℝ) := by
    change (1-(u : ℝ))/2 ≤ (v : ℝ) ↔ 1-(u : ℝ) ≤ 2*(v : ℝ)
    constructor <;> intro h <;> linarith
  simp_rw [he]
  rw [integral_unit_reflection (fun u : I => if (u : ℝ) ≤ 2*(v : ℝ) then (1 : ℝ) else 0), integral_unit_le_real]

theorem fold_upper_integral (v : I) :
    (∫ u : I, if foldUpper u ≤ v then (1 : ℝ) else 0) = unitClamp (2*(v : ℝ)-1) := by
  have he (u : I) : foldUpper u ≤ v ↔ (u : ℝ) ≤ 2*(v : ℝ)-1 := by
    change (1+(u : ℝ))/2 ≤ (v : ℝ) ↔ (u : ℝ) ≤ 2*(v : ℝ)-1
    constructor <;> intro h <;> linarith
  simp_rw [he]
  exact integral_unit_le_real _

theorem foldKernel_mean (v : I) : (∫ u : I, foldKernel v u) = (v : ℝ) := by
  unfold foldKernel
  rw [integral_add ((fold_indicator_integrable foldLower continuous_foldLower.measurable v).div_const 2)
      ((fold_indicator_integrable foldUpper continuous_foldUpper.measurable v).div_const 2),
    integral_div, integral_div, fold_lower_integral, fold_upper_integral]
  unfold unitClamp
  rw [max_eq_right (by nlinarith [v.property.1] : 0 ≤ 2*(v : ℝ))]
  by_cases h : (v : ℝ) ≤ 1/2
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    norm_num
  · rw [min_eq_left (by linarith), max_eq_right (by linarith), min_eq_right (by linarith [v.property.2])]
    ring

theorem foldKernel_monotone (u : I) : Monotone (fun v => foldKernel v u) := by
  intro v w hvw
  dsimp only [foldKernel]
  split_ifs <;> norm_num at * <;> order

theorem foldKernel_zero : foldKernel 0 =ᵐ[volume] fun _ => 0 := by
  filter_upwards [(volume : Measure I).ae_ne 1] with u hu
  have hu1 : (u : ℝ) < 1 := lt_of_le_of_ne u.property.2 (fun h => hu (Subtype.ext h))
  have hl : ¬ foldLower u ≤ 0 := by change ¬ (1-(u : ℝ))/2 ≤ 0; linarith
  have hh : ¬ foldUpper u ≤ 0 := by change ¬ (1+(u : ℝ))/2 ≤ 0; linarith [u.property.1]
  simp [foldKernel,hl,hh]

theorem foldKernel_one : foldKernel 1 =ᵐ[volume] fun _ => 1 := by
  exact Filter.Eventually.of_forall fun u => by norm_num [foldKernel, unitInterval.le_one']

noncomputable def foldedUniform : Copula 2 :=
  copulaOfConditionalAE foldKernel foldKernel_integrable foldKernel_monotone foldKernel_zero foldKernel_one foldKernel_mean

theorem foldedUniform_conditionalCDF (v : I) :
    (fun u => foldedUniform.conditionalCDF u v) =ᵐ[volume] foldKernel v :=
  copulaOfConditionalAE_kernel _ _ _ _ _ _ (fun v u => (foldKernel_mem v u).1) v

theorem foldedUniform_cdf (u v : I) :
    foldedUniform.cdf ![u,v] = ∫ t in Iic u, foldKernel v t :=
  copulaOfConditionalAE_cdf _ _ _ _ _ _ u v

end Verification
