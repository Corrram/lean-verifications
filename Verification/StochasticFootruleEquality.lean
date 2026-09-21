import Verification.ThreeLevel
import Verification.StochasticRhoEquality

/-! # Measurable equality classification for the SI xi-footrule bound

The cut functions are the lengths of the one and positive level sets of
the conditional CDF. Both are nondecreasing in the response threshold.
The middle level is recovered from the uniform marginal.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def conditionalOneCut (C : Copula 2) (v : I) : I :=
  ⟨∫ u : I, oneLevel (fun t => C.conditionalCDF t v) u,
    integral_unit_mem (measurable_oneLevel (C.measurable_conditionalCDF_left v)) (oneLevel_mem _)⟩

noncomputable def conditionalPositiveCut (C : Copula 2) (v : I) : I :=
  ⟨∫ u : I, positiveLevel (fun t => C.conditionalCDF t v) u,
    integral_unit_mem (measurable_positiveLevel (C.measurable_conditionalCDF_left v)) (positiveLevel_mem _)⟩

theorem conditionalOneCut_le (C : Copula 2) (v : I) : conditionalOneCut C v ≤ v := by
  change (∫ u : I, oneLevel (fun t => C.conditionalCDF t v) u) ≤ (v : ℝ)
  rw [← C.integral_conditionalCDF v]
  exact integral_mono
    (integrable_unit_bounded (measurable_oneLevel (C.measurable_conditionalCDF_left v)) (oneLevel_mem _))
    (C.integrable_conditionalCDF v)
    (oneLevel_le_self (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩))

theorem le_conditionalPositiveCut (C : Copula 2) (v : I) : v ≤ conditionalPositiveCut C v := by
  change (v : ℝ) ≤ ∫ u : I, positiveLevel (fun t => C.conditionalCDF t v) u
  rw [← C.integral_conditionalCDF v]
  exact integral_mono (C.integrable_conditionalCDF v)
    (integrable_unit_bounded (measurable_positiveLevel (C.measurable_conditionalCDF_left v)) (positiveLevel_mem _))
    (self_le_positiveLevel (fun u => ⟨C.conditionalCDF_nonneg u v, C.conditionalCDF_le_one u v⟩))

theorem conditionalOneCut_monotone (C : Copula 2) : Monotone (conditionalOneCut C) := by
  intro v w hvw
  change (∫ u : I, oneLevel (fun t => C.conditionalCDF t v) u) ≤
    ∫ u : I, oneLevel (fun t => C.conditionalCDF t w) u
  apply integral_mono
    (integrable_unit_bounded (measurable_oneLevel (C.measurable_conditionalCDF_left v)) (oneLevel_mem _))
    (integrable_unit_bounded (measurable_oneLevel (C.measurable_conditionalCDF_left w)) (oneLevel_mem _))
  intro u
  unfold oneLevel
  by_cases hv : C.conditionalCDF u v = 1
  · have hw : C.conditionalCDF u w = 1 := le_antisymm (C.conditionalCDF_le_one u w)
      (by simpa only [hv] using conditionalCDF_monotone_threshold C u hvw)
    simp [hv, hw]
  · simp only [ite_eq_right hv]
    split_ifs <;> norm_num

theorem conditionalPositiveCut_monotone (C : Copula 2) : Monotone (conditionalPositiveCut C) := by
  intro v w hvw
  change (∫ u : I, positiveLevel (fun t => C.conditionalCDF t v) u) ≤
    ∫ u : I, positiveLevel (fun t => C.conditionalCDF t w) u
  apply integral_mono
    (integrable_unit_bounded (measurable_positiveLevel (C.measurable_conditionalCDF_left v)) (positiveLevel_mem _))
    (integrable_unit_bounded (measurable_positiveLevel (C.measurable_conditionalCDF_left w)) (positiveLevel_mem _))
  intro u
  unfold positiveLevel
  by_cases hv : 0 < C.conditionalCDF u v
  · simp [hv, hv.trans_le (conditionalCDF_monotone_threshold C u hvw)]
  · simp only [ite_eq_right hv]
    split_ifs <;> norm_num

noncomputable def conditionalMiddle (C : Copula 2) (v : I) : I :=
  ⟨((v : ℝ) - conditionalOneCut C v) / ((conditionalPositiveCut C v : ℝ) - conditionalOneCut C v), by
    have hA : (conditionalOneCut C v : ℝ) ≤ v := conditionalOneCut_le C v
    have hB : (v : ℝ) ≤ conditionalPositiveCut C v := le_conditionalPositiveCut C v
    refine ⟨div_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr (hA.trans hB)), ?_⟩
    by_cases he : (conditionalPositiveCut C v : ℝ) - conditionalOneCut C v = 0
    · simp [he]
    · exact (div_le_one (lt_of_le_of_ne (sub_nonneg.mpr (hA.trans hB)) (Ne.symm he))).mpr (by linarith)⟩

theorem measurable_conditionalMiddle (C : Copula 2) : Measurable (conditionalMiddle C) := by
  have hA := measurable_subtype_coe.comp (conditionalOneCut_monotone C).measurable
  have hB := measurable_subtype_coe.comp (conditionalPositiveCut_monotone C).measurable
  exact ((measurable_subtype_coe.sub hA).div (hB.sub hA)).subtype_mk

theorem ae_diagonal_moment_eq_iff (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanFootrule ↔
      ∀ᵐ v : I, (∫ u : I, C.conditionalCDF u v ^ 2) = C.cdf ![v, v] := by
  constructor
  · intro he
    have hi : Integrable (fun v : I => C.cdf ![v, v] - ∫ u : I, C.conditionalCDF u v ^ 2) :=
      C.integrable_diagonal_cdf.sub C.integrable_integral_conditionalCDF_sq
    have hz : (∫ v : I, C.cdf ![v, v] - ∫ u : I, C.conditionalCDF u v ^ 2) = 0 := by
      rw [integral_sub C.integrable_diagonal_cdf C.integrable_integral_conditionalCDF_sq]
      unfold Copula.chatterjeeXi Copula.spearmanFootrule at he
      linarith
    have ha := (integral_eq_zero_iff_of_nonneg
      (fun v => sub_nonneg.mpr (conditionalCDF_sq_le_diagonal C hC v)) hi).mp hz
    filter_upwards [ha] with v hv
    simp only [Pi.zero_apply] at hv
    linarith
  · intro ha
    unfold Copula.chatterjeeXi Copula.spearmanFootrule
    rw [integral_congr_ae ha]

theorem conditionalCDF_threeLevel_of_diagonal_moment_eq (C : Copula 2) (hC : C.IsSI) (v : I)
    (heq : (∫ u : I, C.conditionalCDF u v ^ 2) = C.cdf ![v, v]) :
    (fun u => C.conditionalCDF u v) =ᵐ[volume]
      threeLevel (conditionalOneCut C v) (conditionalPositiveCut C v) (conditionalMiddle C v) := by
  obtain ⟨g, hg, hb, he⟩ := conditionalCDF_antitone_version C hC v
  have hm : (∫ u : I, g u) = (v : ℝ) :=
    (integral_congr_ae he).symm.trans (C.integral_conditionalCDF v)
  have hsq : (∫ u : I, C.conditionalCDF u v ^ 2) = ∫ u : I, g u ^ 2 :=
    integral_congr_ae (he.fun_comp (fun z : ℝ => z ^ 2))
  have hlow : (∫ u in Iic v, g u) = C.cdf ![v, v] := by
    rw [C.cdf_eq_integral_conditionalCDF]
    exact integral_congr_ae (ae_restrict_of_ae he.symm)
  have hvals := ae_three_values_of_diagonal_moment_eq hg hb v hm
    (hsq.symm.trans (heq.trans hlow.symm))
  have hA : (∫ u : I, oneLevel g u) = (conditionalOneCut C v : ℝ) := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    simp only [oneLevel, hu]
  have hB : (∫ u : I, positiveLevel g u) = (conditionalPositiveCut C v : ℝ) := by
    apply integral_congr_ae
    filter_upwards [he] with u hu
    simp only [positiveLevel, hu]
  have hr := ae_threeLevel_of_three_values hg hb ⟨g v, hb v⟩ hvals
    (conditionalOneCut C v) (conditionalPositiveCut C v) hA hB
  have hmean : (∫ u : I, threeLevel (conditionalOneCut C v) (conditionalPositiveCut C v) (g v) u) = (v : ℝ) :=
    (integral_congr_ae hr).symm.trans hm
  have hn := threeLevel_eq_normalized _ _ (g v) v hmean
  filter_upwards [he, hr] with u hu hru
  rw [hu, hru]
  exact congrFun hn u

/-- A three-level representation with ordered cuts implies equality even
without separately assuming SI. -/
theorem xi_eq_footrule_of_threeLevel (C : Copula 2) (A B a : I → I)
    (hAB : ∀ v, A v ≤ B v)
    (hr : ∀ᵐ v : I, (fun u => C.conditionalCDF u v) =ᵐ[volume] threeLevel (A v) (B v) (a v)) :
    C.chatterjeeXi = C.spearmanFootrule := by
  have ha : (fun v : I => ∫ u : I, C.conditionalCDF u v ^ 2) =ᵐ[volume] fun v => C.cdf ![v, v] := by
    filter_upwards [hr] with v hv
    have hm : (∫ u : I, threeLevel (A v) (B v) (a v) u) = (v : ℝ) :=
      (integral_congr_ae hv).symm.trans (C.integral_conditionalCDF v)
    rw [C.cdf_eq_integral_conditionalCDF]
    calc
      _ = ∫ u : I, threeLevel (A v) (B v) (a v) u ^ 2 :=
        integral_congr_ae (hv.fun_comp (fun z : ℝ => z ^ 2))
      _ = ∫ u in Iic v, threeLevel (A v) (B v) (a v) u := threeLevel_moment_eq _ _ (hAB v) _ v hm
      _ = _ := integral_congr_ae (ae_restrict_of_ae hv.symm)
  unfold Copula.chatterjeeXi Copula.spearmanFootrule
  rw [integral_congr_ae ha]

/-- Proposition 2.2 with canonical measurable, nondecreasing cut functions. -/
theorem si_xi_eq_footrule_iff_ordered_threeLevel (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanFootrule ↔
      ∃ A B a : I → I, Monotone A ∧ Monotone B ∧ Measurable A ∧ Measurable B ∧
        Measurable a ∧ (∀ v, A v ≤ B v) ∧
        ∀ᵐ v : I, (fun u => C.conditionalCDF u v) =ᵐ[volume] threeLevelOpen (A v) (B v) (a v) := by
  constructor
  · intro he
    refine ⟨conditionalOneCut C, conditionalPositiveCut C, conditionalMiddle C,
      conditionalOneCut_monotone C, conditionalPositiveCut_monotone C,
      (conditionalOneCut_monotone C).measurable, (conditionalPositiveCut_monotone C).measurable,
      measurable_conditionalMiddle C, fun v => (conditionalOneCut_le C v).trans (le_conditionalPositiveCut C v), ?_⟩
    filter_upwards [(ae_diagonal_moment_eq_iff C hC).mp he] with v hv
    exact (conditionalCDF_threeLevel_of_diagonal_moment_eq C hC v hv).trans
      (threeLevel_eq_open_ae _ _ ((conditionalOneCut_le C v).trans (le_conditionalPositiveCut C v)) _)
  · rintro ⟨A, B, a, _, _, _, _, _, hAB, hr⟩
    apply xi_eq_footrule_of_threeLevel C A B a hAB
    filter_upwards [hr] with v hv
    exact hv.trans (threeLevel_eq_open_ae _ _ (hAB v) _).symm

/-- The open-interval representation implies equality without an ordering
hypothesis on the supplied cuts: replace B with max A B. -/
theorem xi_eq_footrule_of_threeLevelOpen (C : Copula 2) (A B a : I → I)
    (hr : ∀ᵐ v : I, (fun u => C.conditionalCDF u v) =ᵐ[volume] threeLevelOpen (A v) (B v) (a v)) :
    C.chatterjeeXi = C.spearmanFootrule := by
  apply xi_eq_footrule_of_threeLevel C A (fun v => max (A v) (B v)) a (fun v => le_max_left _ _)
  filter_upwards [hr] with v hv
  have hn := threeLevel_eq_open_ae (A v) (max (A v) (B v)) (le_max_left _ _) (a v)
  rw [threeLevelOpen_max] at hn
  exact hv.trans hn.symm

/-- The exact existential representation in Proposition 2.2. -/
theorem si_xi_eq_footrule_iff_threeLevel (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanFootrule ↔
      ∃ A B a : I → I, Monotone A ∧ Monotone B ∧ Measurable A ∧ Measurable B ∧
        Measurable a ∧
        ∀ᵐ v : I, (fun u => C.conditionalCDF u v) =ᵐ[volume] threeLevelOpen (A v) (B v) (a v) := by
  constructor
  · intro he
    obtain ⟨A, B, a, hA, hB, hmA, hmB, hma, _, hr⟩ :=
      (si_xi_eq_footrule_iff_ordered_threeLevel C hC).mp he
    exact ⟨A, B, a, hA, hB, hmA, hmB, hma, hr⟩
  · rintro ⟨A, B, a, _, _, _, _, _, hr⟩
    exact xi_eq_footrule_of_threeLevelOpen C A B a hr

theorem si_xi_eq_footrule_iff_derivative_threeLevel (C : Copula 2) (hC : C.IsSI) :
    C.chatterjeeXi = C.spearmanFootrule ↔
      ∃ A B a : I → I, Monotone A ∧ Monotone B ∧ Measurable A ∧ Measurable B ∧
        Measurable a ∧
        ∀ᵐ v : I, (fun u : I => deriv (Copula.cdfSection C v) (u : ℝ)) =ᵐ[volume]
          threeLevelOpen (A v) (B v) (a v) := by
  rw [si_xi_eq_footrule_iff_threeLevel C hC]
  constructor
  · rintro ⟨A, B, a, hA, hB, hmA, hmB, hma, hr⟩
    refine ⟨A, B, a, hA, hB, hmA, hmB, hma, ?_⟩
    filter_upwards [hr] with v hv
    exact (C.conditionalCDF_eq_deriv v).symm.trans hv
  · rintro ⟨A, B, a, hA, hB, hmA, hmB, hma, hr⟩
    refine ⟨A, B, a, hA, hB, hmA, hmB, hma, ?_⟩
    filter_upwards [hr] with v hv
    exact (C.conditionalCDF_eq_deriv v).trans hv

end Verification
