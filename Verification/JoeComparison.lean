import Verification.JoeConditional
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set

namespace Verification

noncomputable def joeComparisonBase (t : ℝ) : ℝ := 1-Real.exp (-t)
noncomputable def joeComparison (r t : ℝ) : ℝ := -Real.log (1-(joeComparisonBase t)^r)
noncomputable def joeComparisonDeriv (r t : ℝ) : ℝ :=
  r*Real.exp (-t)*(joeComparisonBase t)^r/(joeComparisonBase t*(1-(joeComparisonBase t)^r))

theorem joeComparison_deriv (r t : ℝ) (ha : 0 < joeComparisonBase t)
    (hd : 1-(joeComparisonBase t)^r ≠ 0) :
    HasDerivAt (joeComparison r) (joeComparisonDeriv r t) t := by
  have hA := ((((hasDerivAt_id t).neg).exp).const_sub 1)
  have hP := hA.rpow_const (p := r) (Or.inl ha.ne')
  have hh := ((hP.const_sub 1).log hd).neg
  convert hh using 1
  · rfl
  · dsimp [joeComparisonDeriv]
    change r*Real.exp (-t)*(joeComparisonBase t)^r/(joeComparisonBase t*(1-(joeComparisonBase t)^r)) =
      -(-(-(Real.exp (-t)*(-1))*r*(joeComparisonBase t)^(r-1))/(1-(joeComparisonBase t)^r))
    rw [Real.rpow_sub_one ha.ne']
    field_simp

theorem joeComparison_deriv2 (r t : ℝ) (ha : 0 < joeComparisonBase t)
    (hd : 1-(joeComparisonBase t)^r ≠ 0) :
    HasDerivAt (joeComparisonDeriv r)
      (r*Real.exp (-t)*(joeComparisonBase t)^r*(r*Real.exp (-t)-1+(joeComparisonBase t)^r)/
        ((joeComparisonBase t)^2*(1-(joeComparisonBase t)^r)^2)) t := by
  have hE := ((hasDerivAt_id t).neg).exp
  have hA := hE.const_sub 1
  have hP := hA.rpow_const (p := r) (Or.inl ha.ne')
  have hh := (((hE.const_mul r).mul hP).div (hA.mul (hP.const_sub 1)) (mul_ne_zero ha.ne' hd))
  convert hh using 1
  · rfl
  · dsimp [joeComparisonBase] at ha hd ⊢
    rw [Real.rpow_sub_one ha.ne']
    field_simp
    ring

theorem joeComparison_convex (r : ℝ) (hr : 1 ≤ r) : ConvexOn ℝ (Ici 0) (joeComparison r) := by
  have hb (t : ℝ) (ht : t ∈ Ici 0) : 0 ≤ joeComparisonBase t ∧ joeComparisonBase t < 1 := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (show 0 ≤ t from ht))
    dsimp [joeComparisonBase]
    constructor <;> linarith [Real.exp_pos (-t)]
  have hd (t : ℝ) (ht : t ∈ Ici 0) : 0 < 1-(joeComparisonBase t)^r :=
    sub_pos.mpr (Real.rpow_lt_one (hb t ht).1 (hb t ht).2 (by linarith))
  have ha (t : ℝ) (ht : t ∈ interior (Ici 0)) : 0 < joeComparisonBase t := by
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht0))
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · unfold joeComparison
    apply ContinuousOn.neg
    apply ContinuousOn.log
    · have hc : Continuous (fun t => 1-(joeComparisonBase t)^r) :=
        continuous_const.sub ((by unfold joeComparisonBase; fun_prop : Continuous joeComparisonBase).rpow_const
          (fun _ => Or.inr (by linarith : 0 ≤ r)))
      exact hc.continuousOn
    · intro t ht; exact (hd t ht).ne'
  · intro t ht
    exact (joeComparison_deriv r t (ha t ht) (hd t (interior_subset ht)).ne').hasDerivWithinAt
  · intro t ht
    exact (joeComparison_deriv2 r t (ha t ht) (hd t (interior_subset ht)).ne').hasDerivWithinAt
  · intro t ht
    have hh := one_add_mul_self_le_rpow_one_add
      (show -1 ≤ joeComparisonBase t-1 by linarith [ha t ht]) hr
    rw [show 1+(joeComparisonBase t-1) = joeComparisonBase t by ring] at hh
    have hn : 0 ≤ r*Real.exp (-t)-1+(joeComparisonBase t)^r := by
      unfold joeComparisonBase at hh ⊢
      nlinarith
    exact div_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (by linarith : 0 ≤ r) (Real.exp_pos _).le)
        (Real.rpow_nonneg (ha t ht).le _)) hn) (by positivity)

theorem joeComparison_superadd (r : ℝ) (hr : 1 ≤ r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    joeComparison r s+joeComparison r t ≤ joeComparison r (s+t) := by
  have hzero : joeComparison r 0 = 0 := by simp [joeComparison, joeComparisonBase, Real.zero_rpow (by linarith : r ≠ 0)]
  rcases eq_or_lt_of_le hs with he | hs'
  · subst s; simp [hzero]
  rcases eq_or_lt_of_le ht with he | ht'
  · subst t; simp [hzero]
  have hc := joeComparison_convex r hr
  have h₁ := hc.secant_mono_aux1 (show (0:ℝ) ∈ Ici 0 by simp)
    (show s+t ∈ Ici 0 from add_nonneg hs ht) hs' (by linarith : s < s+t)
  have h₂ := hc.secant_mono_aux1 (show (0:ℝ) ∈ Ici 0 by simp)
    (show s+t ∈ Ici 0 from add_nonneg hs ht) ht' (by linarith : t < s+t)
  rw [hzero] at h₁ h₂
  nlinarith

theorem joe_power_comparison (r : ℝ) (hr : 1 ≤ r) {a b : ℝ}
    (ha : a ∈ Ico 0 1) (hb : b ∈ Ico 0 1) : a^r+b^r-a^r*b^r ≤ (a+b-a*b)^r := by
  let s : ℝ := -Real.log (1-a)
  let t : ℝ := -Real.log (1-b)
  have ha0 : 0 ≤ a := ha.1
  have hb0 : 0 ≤ b := hb.1
  have ha1 : a < 1 := ha.2
  have hb1 : b < 1 := hb.2
  have hs : 0 ≤ s := neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have ht : 0 ≤ t := neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have hes : Real.exp (-s) = 1-a := by dsimp [s]; rw [neg_neg, Real.exp_log (by linarith)]
  have het : Real.exp (-t) = 1-b := by dsimp [t]; rw [neg_neg, Real.exp_log (by linarith)]
  have hbaseS : joeComparisonBase s = a := by simp [joeComparisonBase, hes]
  have hbaseT : joeComparisonBase t = b := by simp [joeComparisonBase, het]
  have hbaseST : joeComparisonBase (s+t) = a+b-a*b := by
    unfold joeComparisonBase
    rw [neg_add, Real.exp_add, hes, het]
    ring
  have hS0 : 0 ≤ a+b-a*b := by nlinarith [mul_nonneg hb0 (sub_nonneg.mpr ha1.le)]
  have hS1 : a+b-a*b < 1 := by nlinarith [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr hb1)]
  have hp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hA : 0 < 1-a^r := sub_pos.mpr (Real.rpow_lt_one ha0 ha1 hp)
  have hB : 0 < 1-b^r := sub_pos.mpr (Real.rpow_lt_one hb0 hb1 hp)
  have hS : 0 < 1-(a+b-a*b)^r := sub_pos.mpr (Real.rpow_lt_one hS0 hS1 hp)
  have hi := joeComparison_superadd r hr hs ht
  unfold joeComparison at hi
  rw [hbaseS, hbaseT, hbaseST] at hi
  have hl : Real.log (1-(a+b-a*b)^r) ≤ Real.log (1-a^r)+Real.log (1-b^r) := by linarith
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_add, Real.exp_log hA, Real.exp_log hB, Real.exp_log hS] at he
  nlinarith

end Verification
