import Verification.BB1Conditional

open Set

namespace Verification

noncomputable def bbSecond (p q t : ℝ) : ℝ :=
  p*q*t^p/t^2*(1+t^p)^(-q-2)*((1+p*q)*t^p+1-p)

theorem bbPsiDeriv_deriv {p q t : ℝ} (ht : 0 < t) :
    HasDerivAt (bbPsiDeriv p q) (bbSecond p q t) t := by
  have hB : 0 < 1+t^p := by positivity
  have hP := (hasDerivAt_id t).rpow_const (p := p-1) (Or.inl ht.ne')
  have hQ := (((hasDerivAt_id t).rpow_const (p := p) (Or.inl ht.ne')).const_add 1).rpow_const
    (p := -q-1) (Or.inl hB.ne')
  have hh := (hP.const_mul (-p*q)).mul hQ
  convert hh using 1
  · rfl
  · dsimp [bbSecond]
    rw [Real.rpow_sub_one ht.ne' (p-1), Real.rpow_sub_one ht.ne' p,
      show -q-2 = (-q-1)-1 by ring, Real.rpow_sub_one hB.ne' (-q-1)]
    field_simp
    ring

theorem bbSecond_pos {p q t : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) (ht : 0 < t) :
    0 < bbSecond p q t := by
  have ha : 0 < 1+p*q := by positivity
  have hx := mul_pos ha (Real.rpow_pos_of_pos ht p)
  have hb : 0 < (1+p*q)*t^p+1-p := by linarith
  exact mul_pos (mul_pos (div_pos (mul_pos (mul_pos hp hq) (Real.rpow_pos_of_pos ht p))
    (sq_pos_of_pos ht)) (Real.rpow_pos_of_pos (by positivity) _)) hb

noncomputable def bbLogSecondCore (p a t : ℝ) : ℝ :=
  (p-2)*Real.log t+Real.log (a*t^p+1-p)
noncomputable def bbLogSecondCoreDeriv (p a t : ℝ) : ℝ :=
  (p-2)/t+p*(a*t^p)/(t*(a*t^p+1-p))

theorem bbLogSecondCore_deriv {p a t : ℝ} (ht : 0 < t) (hB : a*t^p+1-p ≠ 0) :
    HasDerivAt (bbLogSecondCore p a) (bbLogSecondCoreDeriv p a t) t := by
  have hP := (hasDerivAt_id t).rpow_const (p := p) (Or.inl ht.ne')
  have hh := ((Real.hasDerivAt_log ht.ne').const_mul (p-2)).add
    ((((hP.const_mul a).add_const 1).sub_const p).log hB)
  convert hh using 1
  · rfl
  · dsimp [bbLogSecondCoreDeriv]
    rw [Real.rpow_sub_one ht.ne']
    field_simp

theorem bbLogSecondCore_deriv2 {p a t : ℝ} (ht : 0 < t) (hB : a*t^p+1-p ≠ 0) :
    HasDerivAt (bbLogSecondCoreDeriv p a)
      ((2-p-p*(1-p)*(a*t^p/(a*t^p+1-p))-p^2*(a*t^p/(a*t^p+1-p))^2)/t^2) t := by
  have hT := hasDerivAt_id t
  have hP := hT.rpow_const (p := p) (Or.inl ht.ne')
  have hB' := ((hP.const_mul a).add_const 1).sub_const p
  have hh := ((hasDerivAt_const t (p-2)).div hT ht.ne').add
    (((hP.const_mul a).const_mul p).div (hT.mul hB') (mul_ne_zero ht.ne' hB))
  convert hh using 1
  · rfl
  · dsimp
    rw [Real.rpow_sub_one ht.ne']
    field_simp
    ring

theorem bbLogSecondCore_convex {p a : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (ha : 0 < a) :
    ConvexOn ℝ (Ioi 0) (bbLogSecondCore p a) := by
  have hB (t : ℝ) (ht : 0 < t) : 0 < a*t^p+1-p := by
    have hh := mul_pos ha (Real.rpow_pos_of_pos ht p)
    linarith
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
  · intro t ht; exact (bbLogSecondCore_deriv ht (hB t ht).ne').continuousAt.continuousWithinAt
  · intro t ht; exact (bbLogSecondCore_deriv (interior_subset ht) (hB t (interior_subset ht)).ne').hasDerivWithinAt
  · intro t ht; exact (bbLogSecondCore_deriv2 (interior_subset ht) (hB t (interior_subset ht)).ne').hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := interior_subset ht
    have hY := mul_pos ha (Real.rpow_pos_of_pos ht0 p)
    have hR0 : 0 ≤ a*t^p/(a*t^p+1-p) := div_nonneg hY.le (hB t ht0).le
    have hR1 : a*t^p/(a*t^p+1-p) ≤ 1 := (div_le_one (hB t ht0)).mpr (by linarith)
    have hR2 : (a*t^p/(a*t^p+1-p))^2 ≤ 1 := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_left hR1 (mul_nonneg hp.le (sub_nonneg.mpr hp1))
    have h₂ := mul_le_mul_of_nonneg_left hR2 (sq_nonneg p)
    apply div_nonneg _ (sq_nonneg t)
    nlinarith

theorem bbSecond_logconvex {p q : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hq : 0 < q) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (bbSecond p q t)) := by
  have hc := bbLogSecondCore_convex hp hp1 (show 0 < 1+p*q by positivity)
  have hd := ((convex_neg_log_one_add_power hp.le hp1).subset Ioi_subset_Ici_self (convex_Ioi 0)).smul
    (show 0 ≤ q+2 by linarith)
  apply ((hc.add hd).add_const (Real.log (p*q))).congr
  intro t ht
  have hY := mul_pos (mul_pos hp hq) (Real.rpow_pos_of_pos ht p)
  have hA : 0 < 1+t^p := by linarith [Real.rpow_pos_of_pos (show 0 < t from ht) p]
  have hB : 0 < (1+p*q)*t^p+1-p := by
    have hh : 0 < (1+p*q)*t^p := mul_pos (by positivity) (Real.rpow_pos_of_pos ht p)
    linarith
  change bbLogSecondCore p (1+p*q) t+(q+2)*(-Real.log (1+t^p))+Real.log (p*q) = _
  unfold bbLogSecondCore bbSecond
  dsimp only
  rw [Real.log_mul (mul_ne_zero (div_ne_zero hY.ne' (pow_ne_zero _ ht.ne'))
      (Real.rpow_pos_of_pos hA _).ne') hB.ne',
    Real.log_mul (div_ne_zero hY.ne' (pow_ne_zero _ ht.ne')) (Real.rpow_pos_of_pos hA _).ne',
    Real.log_div hY.ne' (pow_ne_zero _ ht.ne'),
    Real.log_mul (mul_ne_zero hp.ne' hq.ne') (Real.rpow_pos_of_pos ht _).ne',
    Real.log_rpow ht, Real.log_rpow hA, Real.log_pow]
  ring

end Verification
