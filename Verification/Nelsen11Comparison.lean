import Verification.Nelsen11Dependence
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Set

namespace Verification

noncomputable def n11ComparisonBase (t : ℝ) : ℝ := 2-Real.exp t
noncomputable def n11Comparison (r t : ℝ) : ℝ := Real.log (2-(n11ComparisonBase t)^r)
noncomputable def n11ComparisonDeriv (r t : ℝ) : ℝ :=
  r*Real.exp t*(n11ComparisonBase t)^r/
    (n11ComparisonBase t*(2-(n11ComparisonBase t)^r))

theorem n11Comparison_deriv (r t : ℝ) (ha : 0 < n11ComparisonBase t)
    (hd : 2-(n11ComparisonBase t)^r ≠ 0) :
    HasDerivAt (n11Comparison r) (n11ComparisonDeriv r t) t := by
  have ha' := (Real.hasDerivAt_exp t).const_sub 2
  have hp := ha'.rpow_const (p := r) (Or.inl ha.ne')
  have hh := (hp.const_sub 2).log hd
  convert hh using 1
  · rfl
  · dsimp [n11ComparisonDeriv]
    change r*Real.exp t*(n11ComparisonBase t)^r /
      (n11ComparisonBase t*(2-(n11ComparisonBase t)^r)) =
      -(-Real.exp t*r*(n11ComparisonBase t)^(r-1))/(2-(n11ComparisonBase t)^r)
    rw [Real.rpow_sub_one ha.ne' r]
    field_simp

theorem n11Comparison_deriv2 (r t : ℝ) (ha : 0 < n11ComparisonBase t)
    (hd : 2-(n11ComparisonBase t)^r ≠ 0) :
    HasDerivAt (n11ComparisonDeriv r)
      (2*r*Real.exp t*(n11ComparisonBase t)^r*
        (r*n11ComparisonBase t-2*r+2-(n11ComparisonBase t)^r)/
        ((n11ComparisonBase t)^2*(2-(n11ComparisonBase t)^r)^2)) t := by
  have ha' := (Real.hasDerivAt_exp t).const_sub 2
  have hp := ha'.rpow_const (p := r) (Or.inl ha.ne')
  have hn := ((Real.hasDerivAt_exp t).const_mul r).mul hp
  have hden := ha'.mul (hp.const_sub 2)
  have hh := hn.div hden (mul_ne_zero ha.ne' hd)
  convert hh using 1
  · rfl
  · dsimp [n11ComparisonBase]
    unfold n11ComparisonBase at ha hd
    rw [Real.rpow_sub_one ha.ne' r]
    field_simp
    ring

theorem n11Comparison_concave (r : ℝ) (hr : 1 ≤ r) :
    ConcaveOn ℝ (Icc 0 (Real.log 2)) (n11Comparison r) := by
  have hb (t : ℝ) (ht : t ∈ Icc 0 (Real.log 2)) :
      0 ≤ n11ComparisonBase t ∧ n11ComparisonBase t ≤ 1 := by
    have hl := Real.one_le_exp_iff.mpr ht.1
    have hu := Real.exp_le_exp.mpr ht.2
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at hu
    dsimp [n11ComparisonBase]
    constructor <;> linarith
  have hd (t : ℝ) (ht : t ∈ Icc 0 (Real.log 2)) : 0 < 2-(n11ComparisonBase t)^r := by
    have hh := Real.rpow_le_one (hb t ht).1 (hb t ht).2 (by linarith : 0 ≤ r)
    linarith
  have ha (t : ℝ) (ht : t ∈ interior (Icc 0 (Real.log 2))) : 0 < n11ComparisonBase t := by
    have hh : t < Real.log 2 := (show t ∈ Ioo 0 (Real.log 2) by simpa only [interior_Icc] using ht).2
    have he := Real.exp_lt_exp.mpr hh
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at he
    exact sub_pos.mpr he
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
  · unfold n11Comparison
    apply ContinuousOn.log
    · have hc : Continuous (fun t => 2-(n11ComparisonBase t)^r) :=
        continuous_const.sub ((by unfold n11ComparisonBase; fun_prop : Continuous n11ComparisonBase).rpow_const
          (fun _ => Or.inr (by linarith : 0 ≤ r)))
      exact hc.continuousOn
    · intro t ht; exact (hd t ht).ne'
  · intro t ht
    exact (n11Comparison_deriv r t (ha t ht) (hd t (interior_subset ht)).ne').hasDerivWithinAt
  · intro t ht
    exact (n11Comparison_deriv2 r t (ha t ht) (hd t (interior_subset ht)).ne').hasDerivWithinAt
  · intro t ht
    have hp : 0 ≤ (n11ComparisonBase t)^r := Real.rpow_nonneg (ha t ht).le _
    have hh := one_add_mul_self_le_rpow_one_add
      (show -1 ≤ n11ComparisonBase t-1 by linarith [ha t ht]) hr
    have he : 1+(n11ComparisonBase t-1) = n11ComparisonBase t := by ring
    rw [he] at hh
    have hn : r*n11ComparisonBase t-2*r+2-(n11ComparisonBase t)^r ≤ 0 := by nlinarith
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hn) (by positivity)

theorem n11Comparison_subadd (r : ℝ) (hr : 1 ≤ r) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t ≤ Real.log 2) :
    n11Comparison r (s+t) ≤ n11Comparison r s+n11Comparison r t := by
  have hzero : n11Comparison r 0 = 0 := by norm_num [n11Comparison, n11ComparisonBase]
  rcases eq_or_lt_of_le hs with he | hs'
  · subst s; simp [hzero]
  rcases eq_or_lt_of_le ht with he | ht'
  · subst t; simp [hzero]
  have hc := (n11Comparison_concave r hr).neg
  have h0 : (0:ℝ) ∈ Icc 0 (Real.log 2) := ⟨le_rfl, Real.log_nonneg (by norm_num)⟩
  have hsum : s+t ∈ Icc 0 (Real.log 2) := ⟨by positivity, hst⟩
  have h₁ := hc.secant_mono_aux1 h0 hsum hs' (by linarith : s < s+t)
  have h₂ := hc.secant_mono_aux1 h0 hsum ht' (by linarith : t < s+t)
  dsimp at h₁ h₂
  rw [hzero] at h₁ h₂
  nlinarith

theorem n11_power_comparison (r : ℝ) (hr : 1 ≤ r) {a b : ℝ}
    (ha : a ∈ Icc 0 1) (hb : b ∈ Icc 0 1) :
    max 0 (2-(2-a^r)*(2-b^r)) ≤ (max 0 (2-(2-a)*(2-b)))^r := by
  have ha0' : 0 ≤ a := ha.1
  have ha1 : a ≤ 1 := ha.2
  have hb0' : 0 ≤ b := hb.1
  have hb1 : b ≤ 1 := hb.2
  have har : a^r ≤ a := by simpa using Real.rpow_le_rpow_of_exponent_ge' ha.1 ha.2 zero_le_one hr
  have hbr : b^r ≤ b := by simpa using Real.rpow_le_rpow_of_exponent_ge' hb.1 hb.2 zero_le_one hr
  have ha0 := Real.rpow_nonneg ha.1 r
  have hb0 := Real.rpow_nonneg hb.1 r
  have hc1 : 2-(2-a)*(2-b) ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hb.2)]
  by_cases hc : 2-(2-a)*(2-b) ≤ 0
  · have hm : 2-(2-a^r)*(2-b^r) ≤ 0 := by
      have hh := mul_le_mul (show 2-a ≤ 2-a^r by linarith) (show 2-b ≤ 2-b^r by linarith)
        (by linarith : 0 ≤ 2-b) (by linarith : 0 ≤ 2-a^r)
      linarith
    rw [max_eq_left hc, max_eq_left hm, Real.zero_rpow (by linarith : r ≠ 0)]
  have hc0 : 0 < 2-(2-a)*(2-b) := lt_of_not_ge hc
  have hs : 0 ≤ Real.log (2-a) := Real.log_nonneg (by linarith)
  have ht : 0 ≤ Real.log (2-b) := Real.log_nonneg (by linarith)
  have habpos : 0 < (2-a)*(2-b) := mul_pos (by linarith) (by linarith)
  have hsum : Real.log (2-a)+Real.log (2-b) ≤ Real.log 2 := by
    rw [← Real.log_mul (by linarith : 2-a ≠ 0) (by linarith : 2-b ≠ 0)]
    exact Real.log_le_log habpos (by linarith)
  have hh := n11Comparison_subadd r hr hs ht hsum
  unfold n11Comparison n11ComparisonBase at hh
  rw [Real.exp_add, Real.exp_log (by linarith : 0 < 2-a),
    Real.exp_log (by linarith : 0 < 2-b)] at hh
  simp only [sub_sub_cancel] at hh
  have haD : 0 < 2-a^r := by linarith [ha.2]
  have hbD : 0 < 2-b^r := by linarith [hb.2]
  have hcD : 0 < 2-(2-(2-a)*(2-b))^r := by
    have hh := Real.rpow_le_one hc0.le hc1 (by linarith : 0 ≤ r)
    linarith
  rw [← Real.log_mul haD.ne' hbD.ne'] at hh
  have he := (Real.log_le_log_iff hcD (mul_pos haD hbD)).mp hh
  rw [max_eq_right hc0.le]
  apply max_le (Real.rpow_nonneg hc0.le _)
  linarith

end Verification
