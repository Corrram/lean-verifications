import Verification.FoldedUniform
import Verification.UnitPrefixIndicators

/-! # Revealing a central interval inside the symmetric-pair model -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem clipped_midpoint (t z : ℝ) (ht : 0 ≤ t) :
    min t (max 0 ((t+z)/2)) = (t-min t (max 0 (-z))+min t (max 0 z))/2 := by
  by_cases hz : z ≤ -t
  · rw [max_eq_left (by linarith : (t+z)/2 ≤ 0),min_eq_right ht,
      max_eq_right (by linarith : 0 ≤ -z),min_eq_left (by linarith : t ≤ -z),
      max_eq_left (by linarith : z ≤ 0),min_eq_right ht]
    ring
  by_cases hz0 : z ≤ 0
  · rw [max_eq_right (by linarith : 0 ≤ (t+z)/2),min_eq_right (by linarith : (t+z)/2 ≤ t),
      max_eq_right (by linarith : 0 ≤ -z),min_eq_right (by linarith : -z ≤ t),
      max_eq_left hz0,min_eq_right ht]
    ring
  by_cases hzt : z ≤ t
  · rw [max_eq_right (by linarith : 0 ≤ (t+z)/2),min_eq_right (by linarith : (t+z)/2 ≤ t),
      max_eq_left (by linarith : -z ≤ 0),min_eq_right ht,max_eq_right (by linarith : 0 ≤ z),min_eq_right hzt]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ (t+z)/2),min_eq_left (by linarith : t ≤ (t+z)/2),
      max_eq_left (by linarith : -z ≤ 0),min_eq_right ht,max_eq_right (by linarith : 0 ≤ z),min_eq_left (by linarith : t ≤ z)]
    ring

theorem foldKernel_prefix (t v : I) :
    (∫ u in Iic t, foldKernel v u) =
      ((t : ℝ)-min (t : ℝ) (max 0 (1-2*(v : ℝ)))+min (t : ℝ) (max 0 (2*(v : ℝ)-1)))/2 := by
  have hl (u : I) : foldLower u ≤ v ↔ 1-2*(v : ℝ) ≤ (u : ℝ) := by
    change (1-(u : ℝ))/2 ≤ (v : ℝ) ↔ _
    constructor <;> intro h <;> linarith
  have hu (u : I) : foldUpper u ≤ v ↔ (u : ℝ) ≤ 2*(v : ℝ)-1 := by
    change (1+(u : ℝ))/2 ≤ (v : ℝ) ↔ _
    constructor <;> intro h <;> linarith
  unfold foldKernel
  rw [integral_add ((fold_indicator_integrable foldLower continuous_foldLower.measurable v).div_const 2).integrableOn
    ((fold_indicator_integrable foldUpper continuous_foldUpper.measurable v).div_const 2).integrableOn,
    integral_div,integral_div]
  simp_rw [hl,hu]
  rw [integral_prefix_ge_real,integral_prefix_le_real]
  ring

theorem reveal_prefix_eq_fold (t v : I) :
    (∫ u in Iic t, if (1-(t : ℝ))/2+(u : ℝ) ≤ (v : ℝ) then (1 : ℝ) else 0) =
      ∫ u in Iic t, foldKernel v u := by
  have he (u : I) : (1-(t : ℝ))/2+(u : ℝ) ≤ (v : ℝ) ↔ (u : ℝ) ≤ (v : ℝ)-(1-(t : ℝ))/2 := by
    constructor <;> intro h <;> linarith
  simp_rw [he]
  rw [integral_prefix_le_real,foldKernel_prefix]
  have h := clipped_midpoint (t : ℝ) (2*(v : ℝ)-1) t.property.1
  rw [show (v : ℝ)-(1-(t : ℝ))/2 = ((t : ℝ)+(2*(v : ℝ)-1))/2 by ring,
    show 1-2*(v : ℝ) = -(2*(v : ℝ)-1) by ring]
  exact h

noncomputable def partialRevealKernel (t v u : I) : ℝ :=
  if u ≤ t then (if (1-(t : ℝ))/2+(u : ℝ) ≤ (v : ℝ) then 1 else 0) else foldKernel v u

theorem partialRevealKernel_measurable (t : I) :
    Measurable (fun p : I × I => partialRevealKernel t p.1 p.2) := by
  unfold partialRevealKernel
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const)
    (Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const measurable_const)
    foldKernel_measurable

theorem partialRevealKernel_mem (t v u : I) : partialRevealKernel t v u ∈ Icc (0 : ℝ) 1 := by
  unfold partialRevealKernel
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ⟨le_rfl,zero_le_one⟩
  · exact foldKernel_mem v u

theorem partialRevealKernel_integrable (t v : I) : Integrable (partialRevealKernel t v) := by
  refine (integrable_const (1 : ℝ)).mono'
    (((partialRevealKernel_measurable t).comp (by fun_prop : Measurable (fun u : I => (v,u)))).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (partialRevealKernel_mem t v u).1]
    exact (partialRevealKernel_mem t v u).2

theorem partialRevealKernel_mean (t v : I) : (∫ u : I, partialRevealKernel t v u) = (v : ℝ) := by
  have hd : Integrable (fun u : I => if (1-(t : ℝ))/2+(u : ℝ) ≤ (v : ℝ) then (1 : ℝ) else 0) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun u => by split_ifs <;> norm_num
  change (∫ u : I, (Iic t).piecewise (fun u => if (1-(t : ℝ))/2+(u : ℝ) ≤ (v : ℝ) then (1 : ℝ) else 0) (foldKernel v) u) = _
  rw [integral_piecewise measurableSet_Iic hd.integrableOn (foldKernel_integrable v).integrableOn,
    reveal_prefix_eq_fold,integral_add_compl measurableSet_Iic (foldKernel_integrable v),foldKernel_mean]

theorem partialRevealKernel_monotone (t u : I) : Monotone (fun v => partialRevealKernel t v u) := by
  intro v w hvw
  by_cases hu : u ≤ t
  · dsimp only [partialRevealKernel]
    simp only [hu,ite_true]
    have h : (v : ℝ) ≤ w := hvw
    split_ifs
    all_goals norm_num
    all_goals linarith
  · simpa only [partialRevealKernel,hu,ite_false] using foldKernel_monotone u hvw

theorem partialRevealKernel_zero (t : I) : partialRevealKernel t 0 =ᵐ[volume] fun _ => 0 := by
  filter_upwards [(volume : Measure I).ae_ne 0,foldKernel_zero] with u hu hf
  have hu0 : 0 < (u : ℝ) := lt_of_le_of_ne u.property.1 (fun h => hu (Subtype.ext h.symm))
  have hh : ¬ (1-(t : ℝ))/2+(u : ℝ) ≤ 0 := by linarith [t.property.2]
  dsimp only [partialRevealKernel]
  by_cases h : u ≤ t
  · rw [ite_eq_left h]
    exact ite_eq_right hh
  · rw [ite_eq_right h,hf]

theorem partialRevealKernel_one (t : I) : partialRevealKernel t 1 =ᵐ[volume] fun _ => 1 := by
  filter_upwards [foldKernel_one] with u hf
  dsimp only [partialRevealKernel]
  by_cases hu : u ≤ t
  · rw [ite_eq_left hu,ite_eq_left]
    have h : (u : ℝ) ≤ t := hu
    change (1-(t : ℝ))/2+(u : ℝ) ≤ 1
    linarith [t.property.2]
  · rw [ite_eq_right hu,hf]

noncomputable def partialReveal (t : I) : Copula 2 :=
  copulaOfConditionalAE (partialRevealKernel t) (partialRevealKernel_integrable t)
    (partialRevealKernel_monotone t) (partialRevealKernel_zero t) (partialRevealKernel_one t) (partialRevealKernel_mean t)

theorem partialReveal_conditionalCDF (t v : I) :
    (fun u => (partialReveal t).conditionalCDF u v) =ᵐ[volume] partialRevealKernel t v :=
  copulaOfConditionalAE_kernel _ _ _ _ _ _ (fun v u => (partialRevealKernel_mem t v u).1) v

end Verification
