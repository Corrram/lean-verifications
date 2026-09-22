import Verification.RampIntegrals

/-! # Threshold probabilities restricted to a prefix of the unit interval -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem integral_prefix_le_real (t : I) (r : ℝ) :
    (∫ u in Iic t, if (u : ℝ) ≤ r then (1 : ℝ) else 0) = min (t : ℝ) (max 0 r) := by
  classical
  by_cases hr : r < 0
  · have he (u : I) : ¬ (u : ℝ) ≤ r := by linarith [u.property.1]
    simp_rw [ite_eq_right (he _)]
    simp [max_eq_left hr.le,min_eq_right t.property.1]
  have hr0 : 0 ≤ r := le_of_not_gt hr
  rw [max_eq_right hr0]
  by_cases hrt : r ≤ (t : ℝ)
  · let q : I := ⟨r,hr0,hrt.trans t.property.2⟩
    have he : (fun u : I => if (u : ℝ) ≤ r then (1 : ℝ) else 0) = (Iic q).indicator (fun _ => 1) := rfl
    rw [he, setIntegral_indicator measurableSet_Iic]
    have hs : Iic t ∩ Iic q = Iic q := inter_eq_right.mpr (Iic_subset_Iic.mpr hrt)
    rw [hs]
    simp [Measure.real,unitInterval.volume_Iic,q,ENNReal.toReal_ofReal hr0,min_eq_right hrt]
  · have he : EqOn (fun u : I => if (u : ℝ) ≤ r then (1 : ℝ) else 0) (fun _ => 1) (Iic t) := by
      intro u hu
      exact ite_eq_left ((show (u : ℝ) ≤ t from hu).trans (le_of_not_ge hrt))
    rw [setIntegral_congr_fun measurableSet_Iic he]
    simp [Measure.real,unitInterval.volume_Iic,ENNReal.toReal_ofReal t.property.1,min_eq_left (le_of_not_ge hrt)]

theorem integral_prefix_ge_real (t : I) (r : ℝ) :
    (∫ u in Iic t, if r ≤ (u : ℝ) then (1 : ℝ) else 0) =
      (t : ℝ)-min (t : ℝ) (max 0 r) := by
  have hs : {u : I | (u : ℝ) = r}.Subsingleton := fun u hu v hv => Subtype.ext (hu.trans hv.symm)
  have hn : ∀ᵐ u : I, (u : ℝ) ≠ r := (ae_iff).mpr (by simpa only [not_not] using hs.countable.measure_zero (volume : Measure I))
  have he : (fun u : I => if r ≤ (u : ℝ) then (1 : ℝ) else 0) =ᵐ[volume]
      fun u => 1-(if (u : ℝ) ≤ r then (1 : ℝ) else 0) := by
    filter_upwards [hn] with u hu
    by_cases h : (u : ℝ) ≤ r
    · rw [ite_eq_left h, ite_eq_right (by intro hh; exact hu (le_antisymm h hh))]
      norm_num
    · rw [ite_eq_right h, ite_eq_left (le_of_not_ge h)]
      norm_num
  have hi : Integrable (fun u : I => if (u : ℝ) ≤ r then (1 : ℝ) else 0) := by
    refine (integrable_const (1 : ℝ)).mono'
      ((measurable_const.ite (measurableSet_le measurable_subtype_coe measurable_const) measurable_const).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun u => by split_ifs <;> norm_num
  rw [integral_congr_ae (ae_restrict_of_ae he),integral_sub (integrable_const _) hi.integrableOn,integral_prefix_le_real]
  simp [Measure.real,unitInterval.volume_Iic,ENNReal.toReal_ofReal t.property.1]

end Verification
