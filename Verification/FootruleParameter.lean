import Verification.FootruleIntegrals
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Monotonicity and the admissible inverse parameter -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

theorem hasDerivAt_footruleClosed (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt footruleClosed ((2 * r - 1) * (-2 * r ^ 2 + 2 * r + 1) / r ^ 2) r := by
  unfold footruleClosed
  convert! (((((hasDerivAt_id r).pow 2).const_mul (-2)).add
    ((hasDerivAt_id r).const_mul 6)).sub_const 5).add
    ((hasDerivAt_const r (1 : ℝ)).div (hasDerivAt_id r) hr) using 1
  simp only [id_eq]
  field_simp
  ring

theorem hasDerivAt_xiClosed (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt xiClosed
      (-2 * (1 - r) * (2 * r - 1) * (-2 * r ^ 2 + 2 * r + 1) / r ^ 3) r := by
  unfold xiClosed
  convert! (((((((hasDerivAt_id r).pow 2).const_mul (-4)).add
    ((hasDerivAt_id r).const_mul 20)).sub_const 17).add
    ((hasDerivAt_const r (2 : ℝ)).div (hasDerivAt_id r) hr)).sub
    ((hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id r).pow 2) (pow_ne_zero _ hr))).sub
    ((Real.hasDerivAt_log hr).const_mul 12) using 1
  simp only [Pi.pow_apply, id_eq]
  field_simp
  ring

theorem continuousOn_footruleClosed : ContinuousOn footruleClosed (Icc (1 / 2) 1) := by
  intro r hr
  exact (hasDerivAt_footruleClosed r (by linarith [hr.1])).continuousAt.continuousWithinAt

theorem continuousOn_xiClosed : ContinuousOn xiClosed (Icc (1 / 2) 1) := by
  intro r hr
  exact (hasDerivAt_xiClosed r (by linarith [hr.1])).continuousAt.continuousWithinAt

theorem strictMonoOn_footruleClosed : StrictMonoOn footruleClosed (Icc (1 / 2) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) continuousOn_footruleClosed
  intro r hr
  rw [interior_Icc] at hr
  rw [(hasDerivAt_footruleClosed r (by linarith [hr.1])).deriv]
  apply div_pos
  · apply mul_pos (by linarith [hr.1])
    have h := mul_nonneg (show 0 ≤ r by linarith [hr.1]) (show 0 ≤ 1 - r by linarith [hr.2])
    nlinarith
  · exact sq_pos_of_pos (by linarith [hr.1])

theorem strictAntiOn_xiClosed : StrictAntiOn xiClosed (Icc (1 / 2) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) continuousOn_xiClosed
  intro r hr
  rw [interior_Icc] at hr
  rw [(hasDerivAt_xiClosed r (by linarith [hr.1])).deriv]
  have hp : 0 < -2 * r ^ 2 + 2 * r + 1 := by
    have h := mul_nonneg (show 0 ≤ r by linarith [hr.1]) (show 0 ≤ 1 - r by linarith [hr.2])
    nlinarith
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) (by linarith [hr.2]))
        (by linarith [hr.1])) hp
  · exact pow_pos (by linarith [hr.1]) _

theorem continuousOn_relaxedParameter : ContinuousOn relaxedParameter (Icc 0 2) := by
  unfold relaxedParameter
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro μ hμ
  linarith [hμ.1]

theorem strictAntiOn_relaxedParameter : StrictAntiOn relaxedParameter (Icc 0 2) := by
  intro μ hμ ν _ h
  exact div_lt_div_of_pos_left (by norm_num) (by linarith [hμ.1]) (by linarith)

theorem continuousOn_relaxedFootrule : ContinuousOn relaxedFootrule (Icc 0 2) := by
  apply (continuousOn_footruleClosed.comp continuousOn_relaxedParameter relaxedParameter_mem).congr
  exact relaxedFootrule_closed

theorem continuousOn_relaxedXi : ContinuousOn relaxedXi (Icc 0 2) := by
  apply (continuousOn_xiClosed.comp continuousOn_relaxedParameter relaxedParameter_mem).congr
  exact relaxedXi_closed

theorem strictAntiOn_relaxedFootrule : StrictAntiOn relaxedFootrule (Icc 0 2) := by
  intro μ hμ ν hν h
  rw [relaxedFootrule_closed μ hμ, relaxedFootrule_closed ν hν]
  exact strictMonoOn_footruleClosed (relaxedParameter_mem ν hν) (relaxedParameter_mem μ hμ)
    (strictAntiOn_relaxedParameter hμ hν h)

theorem strictMonoOn_relaxedXi : StrictMonoOn relaxedXi (Icc 0 2) := by
  intro μ hμ ν hν h
  rw [relaxedXi_closed μ hμ, relaxedXi_closed ν hν]
  exact strictAntiOn_xiClosed (relaxedParameter_mem ν hν) (relaxedParameter_mem μ hμ)
    (strictAntiOn_relaxedParameter hμ hν h)

theorem relaxed_endpoints :
    relaxedFootrule 0 = 0 ∧ relaxedFootrule 2 = -1 / 2 ∧
      relaxedXi 0 = 0 ∧ relaxedXi 2 = 12 * Real.log 2 - 8 := by
  rw [relaxedFootrule_closed 0 (by norm_num), relaxedFootrule_closed 2 (by norm_num),
    relaxedXi_closed 0 (by norm_num), relaxedXi_closed 2 (by norm_num)]
  norm_num [relaxedParameter, footruleClosed, xiClosed, Real.log_div]
  ring

/-- The inverse is unique on the source's admissible interval, not on all of R. -/
theorem existsUnique_relaxedParameter (y : ℝ) (hy : y ∈ Icc (-1 / 2) 0) :
    ∃! μ : ℝ, μ ∈ Icc 0 2 ∧ relaxedFootrule μ = y := by
  obtain ⟨μ, hμ, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 2)
    continuousOn_relaxedFootrule (by simpa only [relaxed_endpoints.1, relaxed_endpoints.2.1] using hy)
  refine ⟨μ, ⟨hμ, he⟩, ?_⟩
  rintro ν ⟨hν, hνy⟩
  exact strictAntiOn_relaxedFootrule.injOn hν hμ (hνy.trans he.symm)

def footruleCubic (y μ : ℝ) : ℝ := μ ^ 3 - (4 + 2 * y) * μ ^ 2 - (4 + 8 * y) * μ - 8 * y

/-- The cubic and the prescribed footrule equation are equivalent on [0,2]. -/
theorem relaxedFootrule_eq_iff_cubic (y μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    relaxedFootrule μ = y ↔ footruleCubic y μ = 0 := by
  have hd : 2 + μ ≠ 0 := by linarith [hμ.1]
  have he : footruleCubic y μ = 2 * (2 + μ) ^ 2 * (relaxedFootrule μ - y) := by
    rw [relaxedFootrule_closed μ hμ]
    unfold footruleClosed relaxedParameter footruleCubic
    field_simp
    ring
  rw [he]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero _ hd)))

/-- Theorem 3.3's cubic has exactly one admissible root for each nonpositive target footrule. -/
theorem existsUnique_footruleCubic (y : ℝ) (hy : y ∈ Icc (-1 / 2) 0) :
    ∃! μ : ℝ, μ ∈ Icc 0 2 ∧ footruleCubic y μ = 0 := by
  obtain ⟨μ, ⟨hμ, he⟩, hu⟩ := existsUnique_relaxedParameter y hy
  refine ⟨μ, ⟨hμ, (relaxedFootrule_eq_iff_cubic y μ hμ).mp he⟩, ?_⟩
  rintro ν ⟨hν, hroot⟩
  exact hu ν ⟨hν, (relaxedFootrule_eq_iff_cubic y ν hν).mpr hroot⟩

/-- Global uniqueness in R would be false: at y=-1/2 there are two distinct real roots. -/
theorem footruleCubic_not_unique_real :
    footruleCubic (-1 / 2) 2 = 0 ∧ footruleCubic (-1 / 2) (-1) = 0 ∧ (2 : ℝ) ≠ -1 := by
  norm_num [footruleCubic]

/-- The universal lower estimate with both coefficients explicitly evaluated. -/
theorem xi_footrule_closed_lower_bound (C : Copula 2) (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    μ * footruleClosed (relaxedParameter μ) + xiClosed (relaxedParameter μ) ≤
      μ * C.spearmanFootrule + C.chatterjeeXi := by
  rw [← relaxedFootrule_closed μ hμ, ← relaxedXi_closed μ hμ]
  exact xi_footrule_relaxed_lower_bound C μ hμ

/-- Explicit lower bound at the unique admissible cubic parameter. -/
theorem xi_lower_bound_of_cubic (C : Copula 2) (y μ : ℝ) (hμ : μ ∈ Icc 0 2)
    (hy : C.spearmanFootrule = y) (hroot : footruleCubic y μ = 0) :
    xiClosed (relaxedParameter μ) ≤ C.chatterjeeXi := by
  rw [← relaxedXi_closed μ hμ]
  apply xi_lower_bound_at_relaxed_footrule C μ hμ
  exact hy.trans ((relaxedFootrule_eq_iff_cubic y μ hμ).mpr hroot).symm

end Verification
