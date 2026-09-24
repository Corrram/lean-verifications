import Verification.Nelsen22Analytic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open ProbabilityTheory Set Copula

namespace Verification

noncomputable def n22Comparison (r t : ℝ) : ℝ := Real.arcsin (1-(1-Real.sin t)^r)
noncomputable def n22ComparisonPrime (r t : ℝ) : ℝ :=
  r*Real.cos t*(1-Real.sin t)^(r-1)/Real.sqrt (1-(1-(1-Real.sin t)^r)^2)
noncomputable def n22ComparisonSquare (r x : ℝ) : ℝ := (2-x)*x^(r-1)/(2-x^r)

theorem n22ComparisonSquare_deriv {r x : ℝ} (hr : 1 ≤ r) (hx : x ∈ Ioo 0 1) :
    HasDerivAt (n22ComparisonSquare r)
      (2*x^(r-2)*(2*(r-1)-r*x+x^r)/(2-x^r)^2) x := by
  have hp : 0 < r := by linarith
  have hb : 0 < 2-x^r := by linarith [Real.rpow_lt_one hx.1.le hx.2 hp]
  have hX := hasDerivAt_id x
  have hh := ((hX.const_sub 2).mul (hX.rpow_const (p := r-1) (Or.inl hx.1.ne'))).div
    ((hX.rpow_const (p := r) (Or.inl hx.1.ne')).const_sub 2) hb.ne'
  have he : x^(r-1) = x^(r-2)*x := by
    rw [show r-1 = (r-2)+1 by ring,Real.rpow_add_one hx.1.ne']
  have he' : x^r = x^(r-2)*x^2 := by
    calc
      _ = x^((r-2)+2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx.1,Real.rpow_two]
  convert hh using 1
  · rfl
  · simp only [Pi.mul_apply,id_eq,show r-1-1 = r-2 by ring,he,he']
    ring

theorem n22ComparisonSquare_monotone {r : ℝ} (hr : 1 ≤ r) :
    MonotoneOn (n22ComparisonSquare r) (Ioo 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · intro x hx; exact (n22ComparisonSquare_deriv hr hx).continuousAt.continuousWithinAt
  · intro x hx; exact (n22ComparisonSquare_deriv hr (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (0:ℝ) 1 := interior_subset hx
    rw [(n22ComparisonSquare_deriv hr hx').deriv]
    have hh := one_add_mul_self_le_rpow_one_add (show -1 ≤ x-1 by linarith [hx'.1]) hr
    rw [add_sub_cancel] at hh
    have hn : 0 ≤ 2*(r-1)-r*x+x^r := by nlinarith
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hx'.1.le _)) hn) (sq_nonneg _)

theorem n22Comparison_deriv {r t : ℝ} (hr : 1 ≤ r) (ht : t ∈ Ioo 0 (Real.pi/2)) :
    HasDerivAt (n22Comparison r) (n22ComparisonPrime r t) t := by
  have hp : 0 < r := by linarith
  have hb := (n22_trig_pos ht).2
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos])
  have hpow := Real.rpow_lt_one hb.le (by linarith : 1-Real.sin t < 1) hp
  have hpos := Real.rpow_pos_of_pos hb r
  have hh := (Real.hasDerivAt_arcsin (x := 1-(1-Real.sin t)^r) (by linarith) (by linarith)).comp t
    (((Real.hasDerivAt_sin t).const_sub 1).rpow_const (p := r) (Or.inl hb.ne') |>.const_sub 1)
  convert hh using 1
  · rfl
  · dsimp [n22ComparisonPrime]
    ring

theorem n22ComparisonPrime_sq {r t : ℝ} (hr : 1 ≤ r) (ht : t ∈ Ioo 0 (Real.pi/2)) :
    n22ComparisonPrime r t ^ 2 = r^2*n22ComparisonSquare r (1-Real.sin t) := by
  let x := 1-Real.sin t
  have hx : x ∈ Ioo (0:ℝ) 1 := ⟨(n22_trig_pos ht).2,by
    dsimp [x]; linarith [Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,Real.pi_pos])]⟩
  have hxr : 0 < x^r := Real.rpow_pos_of_pos hx.1 _
  have hx1 : x^r < 1 := Real.rpow_lt_one hx.1.le hx.2 (by linarith)
  have hb : 0 < 1-(1-x^r)^2 := by nlinarith
  have hcos : Real.cos t^2 = x*(2-x) := by
    dsimp [x]; nlinarith [Real.sin_sq_add_cos_sq t]
  have he : x^(r-1)*x = x^r := by
    rw [← Real.rpow_add_one hx.1.ne',sub_add_cancel]
  change (r*Real.cos t*x^(r-1)/Real.sqrt (1-(1-x^r)^2))^2 = r^2*((2-x)*x^(r-1)/(2-x^r))
  rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hb.le,hcos]
  have hbase : 1-(1-x^r)^2 = x^r*(2-x^r) := by ring
  rw [hbase]
  have hn : r^2*(x*(2-x))*(x^(r-1))^2 = (r^2*((2-x)*x^(r-1)))*x^r := by
    rw [← he]
    ring
  rw [hn,mul_comm (x^r) (2-x^r),mul_div_mul_right _ _ hxr.ne',mul_div_assoc]

theorem n22ComparisonPrime_antitone {r : ℝ} (hr : 1 ≤ r) :
    AntitoneOn (n22ComparisonPrime r) (Ioo 0 (Real.pi/2)) := by
  intro s hs t ht hst
  have hsin : Real.sin s ≤ Real.sin t := Real.monotoneOn_sin
    ⟨by linarith [hs.1,Real.pi_pos],hs.2.le⟩ ⟨by linarith [ht.1,Real.pi_pos],ht.2.le⟩ hst
  have hm (a : ℝ) (ha : a ∈ Ioo 0 (Real.pi/2)) : 1-Real.sin a ∈ Ioo (0:ℝ) 1 :=
    ⟨(n22_trig_pos ha).2,by linarith [Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2,Real.pi_pos])]⟩
  have hh := n22ComparisonSquare_monotone hr (hm t ht) (hm s hs) (sub_le_sub_left hsin 1)
  have hsq := mul_le_mul_of_nonneg_left hh (sq_nonneg r)
  rw [← n22ComparisonPrime_sq hr ht,← n22ComparisonPrime_sq hr hs] at hsq
  have hn (a : ℝ) (ha : a ∈ Ioo 0 (Real.pi/2)) : 0 ≤ n22ComparisonPrime r a := by
    exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (n22_trig_pos ha).1.le)
      (Real.rpow_nonneg (n22_trig_pos ha).2.le _)) (Real.sqrt_nonneg _)
  nlinarith [hn s hs,hn t ht]

theorem n22Comparison_concave {r : ℝ} (hr : 1 ≤ r) :
    ConcaveOn ℝ (Icc 0 (Real.pi/2)) (n22Comparison r) := by
  have hc : Continuous (n22Comparison r) := by
    exact Real.continuous_arcsin.comp (continuous_const.sub
      ((continuous_const.sub Real.continuous_sin).rpow_const (fun _ => Or.inr (by linarith))))
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _) hc.continuousOn
  · intro t ht
    exact (n22Comparison_deriv hr (by simpa only [interior_Icc] using ht)).differentiableAt.differentiableWithinAt
  · intro s hs t ht hst
    have hs' : s ∈ Ioo 0 (Real.pi/2) := by simpa only [interior_Icc] using hs
    have ht' : t ∈ Ioo 0 (Real.pi/2) := by simpa only [interior_Icc] using ht
    rw [(n22Comparison_deriv hr hs').deriv,(n22Comparison_deriv hr ht').deriv]
    exact n22ComparisonPrime_antitone hr hs' ht' hst

theorem n22Comparison_zero (r : ℝ) : n22Comparison r 0 = 0 := by simp [n22Comparison]

theorem n22Comparison_subadd {r s t : ℝ} (hr : 1 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hst : s+t ≤ Real.pi/2) : n22Comparison r (s+t) ≤ n22Comparison r s+n22Comparison r t := by
  by_cases hz : s+t = 0
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0,ht0,n22Comparison_zero]
  have hp : 0 < s+t := lt_of_le_of_ne (add_nonneg hs ht) (Ne.symm hz)
  have hc := n22Comparison_concave hr
  have hcomb : t/(s+t)+s/(s+t) = 1 := by field_simp; ring
  have h₁ := hc.2 (show (0:ℝ) ∈ Icc 0 (Real.pi/2) by constructor; exact le_rfl; positivity) ⟨hp.le,hst⟩
    (div_nonneg ht hp.le) (div_nonneg hs hp.le) hcomb
  have h₂ := hc.2 (show (0:ℝ) ∈ Icc 0 (Real.pi/2) by constructor; exact le_rfl; positivity) ⟨hp.le,hst⟩
    (div_nonneg hs hp.le) (div_nonneg ht hp.le) (by linarith)
  simp only [smul_eq_mul,mul_zero,zero_add,n22Comparison_zero,div_mul_cancel₀ _ hz] at h₁ h₂
  have he : s/(s+t)*n22Comparison r (s+t)+t/(s+t)*n22Comparison r (s+t) = n22Comparison r (s+t) := by field_simp
  linarith

theorem n22Comparison_ge {r t : ℝ} (hr : 1 ≤ r) (ht : t ∈ Icc 0 (Real.pi/2)) :
    t ≤ n22Comparison r t := by
  have hb : 1-Real.sin t ∈ Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr (Real.sin_le_one _),by
    linarith [Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2,Real.pi_pos])]⟩
  have hh := Real.rpow_le_self_of_le_one hb.1 hb.2 hr
  have he := Real.arcsin_le_arcsin (show Real.sin t ≤ 1-(1-Real.sin t)^r by linarith)
  rw [Real.arcsin_sin (by linarith [ht.1,Real.pi_pos]) ht.2] at he
  exact he

end Verification
