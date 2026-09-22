import Verification.FootruleParameter

/-! # The relaxed lower curve lies strictly inside the absolute square-root bound -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def footruleSquareDefect (r : ℝ) := xiClosed r - footruleClosed r ^ 2

theorem hasDerivAt_footruleSquareDefect (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt footruleSquareDefect
      (-4 * (1-r)^3 * (2*r-1) * (-2*r^2+2*r+1) / r^3) r := by
  convert! (hasDerivAt_xiClosed r hr).sub ((hasDerivAt_footruleClosed r hr).pow 2) using 1
  unfold footruleClosed
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  field_simp
  ring

theorem strictAntiOn_footruleSquareDefect :
    StrictAntiOn footruleSquareDefect (Icc (1/2) 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuousOn_xiClosed.sub (continuousOn_footruleClosed.pow 2))
  intro r hr
  rw [interior_Icc] at hr
  change deriv footruleSquareDefect r < 0
  rw [(hasDerivAt_footruleSquareDefect r (by linarith [hr.1])).deriv]
  have hp : 0 < -2*r^2+2*r+1 := by
    have h := mul_nonneg (show 0 ≤ r by linarith [hr.1])
      (show 0 ≤ 1-r by linarith [hr.2])
    nlinarith
  apply div_neg_of_neg_of_pos
  · exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (by norm_num) (pow_pos (by linarith [hr.2]) _))
      (by linarith [hr.1])) hp
  · exact pow_pos (by linarith [hr.1]) _

theorem relaxed_footrule_sq_lt_xi (μ : ℝ) (hμ : μ ∈ Ioc 0 2) :
    relaxedFootrule μ ^ 2 < relaxedXi μ := by
  have hm : μ ∈ Icc 0 2 := ⟨hμ.1.le,hμ.2⟩
  have hr := relaxedParameter_mem μ hm
  have hr1 : relaxedParameter μ < 1 := by
    unfold relaxedParameter
    apply (div_lt_one (by linarith [hμ.1])).mpr
    linarith [hμ.1]
  have h := strictAntiOn_footruleSquareDefect hr (by norm_num) hr1
  have hz : footruleSquareDefect 1 = 0 := by
    norm_num [footruleSquareDefect, xiClosed, footruleClosed]
  rw [hz] at h
  change 0 < xiClosed (relaxedParameter μ) - footruleClosed (relaxedParameter μ)^2 at h
  rw [relaxedFootrule_closed μ hm, relaxedXi_closed μ hm]
  linarith

/-- A negative footrule cannot attain the absolute square-root bound. -/
theorem negative_footrule_sq_lt_xi (C : Copula 2) (hC : C.spearmanFootrule < 0) :
    C.spearmanFootrule ^ 2 < C.chatterjeeXi := by
  obtain ⟨μ, ⟨hμ, he⟩, _⟩ := existsUnique_relaxedParameter C.spearmanFootrule
    ⟨C.spearmanFootrule_mem_Icc.1,hC.le⟩
  have hm : 0 < μ := by
    by_contra hn
    have hz : μ = 0 := le_antisymm (le_of_not_gt hn) hμ.1
    rw [hz, relaxed_endpoints.1] at he
    linarith
  have hs := relaxed_footrule_sq_lt_xi μ ⟨hm,hμ.2⟩
  rw [he] at hs
  exact hs.trans_le (xi_lower_bound_at_relaxed_footrule C μ hμ he.symm)

end Verification
