import Papers.Rockel2026ExactBlest.ExactBlestParameters

/-!
# Blest's coefficient and its transpose

Checks for the corollary on the exact region of `(ν(C), ν(Cᵀ))` in exact-blest-regions.tex,
for the boundary function `Λ` displayed before it, and for the further claims of the revised
manuscript that are not covered by the earlier modules: the derivative bounds on `Υ` used in
the proof of the corollary, the failure of central symmetry of the `(η,ν)`-region, the trivial
bound `1/2` obtained from the `(ρ,ν)`-region alone, and the numerical fibre stated in the
discussion.
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval
open Papers.Rockel2026XiBlest

namespace Papers.Rockel2026ExactBlest

noncomputable section
set_option maxHeartbeats 4000000

/-! ## The randomized branch in transposed coordinates -/

/-- The paper's `n_a = ν(B_aᵀ)`. -/
def transposeParam (a : ℝ) : ℝ := -1 + (1 - a) ^ 4 * (2 * a + 1) / (4 * a ^ 2)

theorem transposeParam_eq (a : ℝ) (ha : a ≠ 0) : transposeParam a = 2 * etaB a - nuB a := by
  unfold transposeParam etaB nuB
  field_simp
  ring

theorem nu_transpose_familyB_param (a : I) (ha : (1 / 2 : ℝ) ≤ a) :
    blestNu (familyB a ha).transpose = transposeParam a := by
  have h0 : (a : ℝ) ≠ 0 := by linarith
  rw [nu_transpose_familyB, transposeParam_eq _ h0]

theorem transposeParam_factor (a : ℝ) (ha : a ≠ 0) :
    transposeParam a = -1 + (1 - a) ^ 4 * (2 * (1 / a) + (1 / a) ^ 2) / 4 := by
  unfold transposeParam
  field_simp

theorem nuB_factor (a : ℝ) (ha : a ≠ 0) : nuB a = -1 + (1 - a) ^ 3 * (1 / a + 1) := by
  unfold nuB
  field_simp

theorem transposeParam_strictAnti : StrictAntiOn transposeParam (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hi : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy.le
  have hs : (1 / y) ^ 2 ≤ (1 / x) ^ 2 := by gcongr
  have hh : 2 * (1 / y) + (1 / y) ^ 2 ≤ 2 * (1 / x) + (1 / x) ^ 2 := by linarith
  have hpos : 0 < 2 * (1 / x) + (1 / x) ^ 2 := by positivity
  have hp : (1 - y) ^ 4 < (1 - x) ^ 4 :=
    pow_lt_pow_left₀ (by linarith) (by linarith [hy.2]) (by norm_num)
  have hnon : 0 ≤ (1 - y) ^ 4 := pow_nonneg (by linarith [hy.2]) 4
  have hmul := mul_le_mul_of_nonneg_left hh hnon
  have hstrict := mul_lt_mul_of_pos_right hp hpos
  rw [transposeParam_factor x hx0.ne', transposeParam_factor y hy0.ne']
  linarith

theorem nuB_strictAnti : StrictAntiOn nuB (Icc (1 / 2 : ℝ) 1) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hi : 1 / y + 1 ≤ 1 / x + 1 := by linarith [one_div_le_one_div_of_le hx0 hxy.le]
  have hpos : 0 < 1 / x + 1 := by positivity
  have hp : (1 - y) ^ 3 < (1 - x) ^ 3 :=
    pow_lt_pow_left₀ (by linarith) (by linarith [hy.2]) (by norm_num)
  have hnon : 0 ≤ (1 - y) ^ 3 := pow_nonneg (by linarith [hy.2]) 3
  have hmul := mul_le_mul_of_nonneg_left hi hnon
  have hstrict := mul_lt_mul_of_pos_right hp hpos
  rw [nuB_factor x hx0.ne', nuB_factor y hy0.ne']
  linarith

theorem transposeParam_endpoints : transposeParam (1 / 2) = -7 / 8 ∧ transposeParam 1 = -1 := by
  norm_num [transposeParam]

theorem nuB_endpoints : nuB (1 / 2) = -5 / 8 ∧ nuB 1 = -1 := by
  norm_num [nuB]

theorem transposeParam_open (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    transposeParam a ∈ Ioo (-1 : ℝ) (-7 / 8) := by
  have hl := transposeParam_strictAnti ⟨ha.le, ha1.le⟩
    (show (1 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) ha1
  have hu := transposeParam_strictAnti (show (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 by norm_num)
    ⟨ha.le, ha1.le⟩ ha
  rw [transposeParam_endpoints.2] at hl
  rw [transposeParam_endpoints.1] at hu
  exact ⟨hl, hu⟩

theorem nuB_open (a : ℝ) (ha : 1 / 2 < a) (ha1 : a < 1) :
    nuB a ∈ Ioo (-1 : ℝ) (-5 / 8) := by
  have hl := nuB_strictAnti ⟨ha.le, ha1.le⟩ (show (1 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) ha1
  have hu := nuB_strictAnti (show (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) ⟨ha.le, ha1.le⟩ ha
  rw [nuB_endpoints.2] at hl
  rw [nuB_endpoints.1] at hu
  exact ⟨hl, hu⟩

theorem transposeParam_range (a : I) (ha : (1 / 2 : ℝ) ≤ a) :
    transposeParam a ∈ Icc (-1 : ℝ) (-7 / 8) := by
  have hl := transposeParam_strictAnti.antitoneOn ⟨ha, a.property.2⟩
    (show (1 : ℝ) ∈ Icc (1 / 2) 1 by norm_num) a.property.2
  have hu := transposeParam_strictAnti.antitoneOn (show (1 / 2 : ℝ) ∈ Icc (1 / 2) 1 by norm_num)
    ⟨ha, a.property.2⟩ ha
  rw [transposeParam_endpoints.2] at hl
  rw [transposeParam_endpoints.1] at hu
  exact ⟨hl, hu⟩

theorem transposeParam_exists_unique (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) (-7 / 8)) :
    ∃! a : I, (1 / 2 : ℝ) ≤ a ∧ transposeParam a = n := by
  have hc : Continuous (fun t : I => -transposeParam ((1 + (t : ℝ)) / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have ht : 0 < 1 + (t : ℝ) := by linarith [t.property.1]
    unfold transposeParam
    fun_prop (disch := positivity)
  obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := -n)
    (by norm_num [transposeParam]; linarith [hn.2]) (by norm_num [transposeParam]; linarith [hn.1])
  let a : I := ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have ha : (1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith [t.property.1]
  have hv : transposeParam a = n := by change transposeParam ((1 + (t : ℝ)) / 2) = n; linarith
  refine ⟨a, ⟨ha, hv⟩, ?_⟩
  intro b hb
  apply Subtype.ext
  apply transposeParam_strictAnti.injOn ⟨hb.1, b.property.2⟩ ⟨ha, a.property.2⟩
  exact hb.2.trans hv.symm

/-- The paper's statement that `a ↦ n_a` decreases bijectively from `(1/2,1)` onto `(-1,-7/8)`. -/
theorem transposeParam_bijOn :
    StrictAntiOn transposeParam (Ioo (1 / 2 : ℝ) 1) ∧
      BijOn transposeParam (Ioo (1 / 2 : ℝ) 1) (Ioo (-1 : ℝ) (-7 / 8)) := by
  have hanti : StrictAntiOn transposeParam (Ioo (1 / 2 : ℝ) 1) :=
    transposeParam_strictAnti.mono Ioo_subset_Icc_self
  refine ⟨hanti, fun a ha => transposeParam_open a ha.1 ha.2, hanti.injOn, ?_⟩
  intro n hn
  obtain ⟨a, ha, _⟩ := transposeParam_exists_unique n ⟨hn.1.le, hn.2.le⟩
  have hl : (1 / 2 : ℝ) < a := by
    rcases ha.1.eq_or_lt with h | h
    · have := ha.2; rw [← h, transposeParam_endpoints.1] at this; linarith [hn.2]
    · exact h
  have hu : (a : ℝ) < 1 := by
    rcases a.property.2.eq_or_lt with h | h
    · have := ha.2; rw [h, transposeParam_endpoints.2] at this; linarith [hn.1]
    · exact h
  exact ⟨a, ⟨hl, hu⟩, ha.2⟩

/-- The randomized parameter belonging to a value of `ν` in the transposed coordinates. -/
def lambdaParameter (n : ℝ) : I :=
  if hn : n ∈ Icc (-1 : ℝ) (-7 / 8) then (transposeParam_exists_unique n hn).choose else 0

theorem lambdaParameter_spec (n : ℝ) (hn : n ∈ Icc (-1 : ℝ) (-7 / 8)) :
    (1 / 2 : ℝ) ≤ lambdaParameter n ∧ transposeParam (lambdaParameter n) = n := by
  rw [lambdaParameter, dite_eq_left hn]
  exact (transposeParam_exists_unique n hn).choose_spec.1

theorem lambdaParameter_value (a : I) (ha : (1 / 2 : ℝ) ≤ a) :
    lambdaParameter (transposeParam a) = a := by
  have hn := transposeParam_range a ha
  rw [lambdaParameter, dite_eq_left hn]
  exact ((transposeParam_exists_unique _ hn).choose_spec.2 a ⟨ha, rfl⟩).symm

theorem lambdaParameter_open (n : ℝ) (hn : n ∈ Ioo (-1 : ℝ) (-7 / 8)) :
    (1 / 2 : ℝ) < lambdaParameter n ∧ (lambdaParameter n : ℝ) < 1 := by
  obtain ⟨ha, hv⟩ := lambdaParameter_spec n ⟨hn.1.le, hn.2.le⟩
  constructor
  · rcases ha.eq_or_lt with h | h
    · rw [← h, transposeParam_endpoints.1] at hv; linarith [hn.2]
    · exact h
  · rcases (lambdaParameter n).property.2.eq_or_lt with h | h
    · rw [h, transposeParam_endpoints.2] at hv; linarith [hn.1]
    · exact h

/-! ## The boundary function `Λ` -/

/-- The closed-form branch of the paper's `Λ`. -/
def lambdaClosed (n : ℝ) : ℝ := 4 * ((1 + n) / 2) ^ (3 / 4 : ℝ) - n - 2

/-- The paper's `Λ`: equal to `-1` at `-1`, parametric on `(-1,-7/8)`, closed form on
`[-7/8,1]`. Values outside `[-1,1]` play no role. -/
def Lambda (n : ℝ) : ℝ :=
  if n ≤ -1 then -1 else if n < -7 / 8 then nuB (lambdaParameter n) else lambdaClosed n

theorem Lambda_neg_one : Lambda (-1) = -1 := by
  simp [Lambda]

theorem Lambda_param_branch (n : ℝ) (hn : n ∈ Ioo (-1 : ℝ) (-7 / 8)) :
    Lambda n = nuB (lambdaParameter n) := by
  rw [Lambda, ite_eq_right (not_le.mpr hn.1), ite_eq_left hn.2]

theorem Lambda_closed_branch (n : ℝ) (hn : -7 / 8 ≤ n) : Lambda n = lambdaClosed n := by
  rw [Lambda, ite_eq_right (show ¬ n ≤ -1 by linarith), ite_eq_right (not_lt.mpr hn)]

theorem rpow_fourth_three_quarters (s : ℝ) (hs : 0 ≤ s) : (s ^ 4) ^ (3 / 4 : ℝ) = s ^ 3 := by
  rw [← Real.rpow_natCast s 4, ← Real.rpow_mul hs]
  norm_num

theorem fourthRoot_pow (x : ℝ) (hx : 0 ≤ x) : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem lambdaClosed_param (s : ℝ) (hs : 0 ≤ s) :
    lambdaClosed (2 * s ^ 4 - 1) = 4 * s ^ 3 - 2 * s ^ 4 - 1 := by
  unfold lambdaClosed
  have h : (1 + (2 * s ^ 4 - 1)) / 2 = s ^ 4 := by ring
  rw [h, rpow_fourth_three_quarters s hs]
  ring

/-- Every `n ≥ -1` is `2 s^4 - 1` for the nonnegative fourth root `s = ((1+n)/2)^{1/4}`. -/
theorem closed_root (n : ℝ) (hn : -1 ≤ n) :
    0 ≤ ((1 + n) / 2) ^ (1 / 4 : ℝ) ∧ n = 2 * (((1 + n) / 2) ^ (1 / 4 : ℝ)) ^ 4 - 1 := by
  have hx : 0 ≤ (1 + n) / 2 := by linarith
  refine ⟨Real.rpow_nonneg hx _, ?_⟩
  rw [fourthRoot_pow _ hx]
  ring

/-- The quartic `4 s^3 - 2 s^4` is strictly increasing on `[0,1]`. -/
theorem quartic_strictMono (s t : ℝ) (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    4 * s ^ 3 - 2 * s ^ 4 < 4 * t ^ 3 - 2 * t ^ 4 := by
  have key : (4 * t ^ 3 - 2 * t ^ 4) - (4 * s ^ 3 - 2 * s ^ 4) =
      (t - s) * (4 * t * s + 2 * (t ^ 2 + s ^ 2) * (2 - t - s)) := by ring
  have h1 : 0 < t - s := by linarith
  have h2 : 0 < 2 * (t ^ 2 + s ^ 2) * (2 - t - s) := by
    have : 0 < t := by linarith
    have : 0 < t ^ 2 + s ^ 2 := by positivity
    have : 0 < 2 - t - s := by linarith
    positivity
  have h3 : 0 ≤ 4 * t * s := by
    have : 0 < t := by linarith
    positivity
  nlinarith

theorem root_bounds (n : ℝ) (hn : n ∈ Icc (-7 / 8 : ℝ) 1) :
    1 / 2 ≤ ((1 + n) / 2) ^ (1 / 4 : ℝ) ∧ ((1 + n) / 2) ^ (1 / 4 : ℝ) ≤ 1 := by
  obtain ⟨hs0, hs⟩ := closed_root n (by linarith [hn.1])
  set s := ((1 + n) / 2) ^ (1 / 4 : ℝ) with hsdef
  constructor
  · by_contra h
    push Not at h
    have : s ^ 4 < (1 / 2) ^ 4 := pow_lt_pow_left₀ h hs0 (by norm_num)
    linarith [hn.1]
  · by_contra h
    push Not at h
    have : (1 : ℝ) ^ 4 < s ^ 4 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
    linarith [hn.2]

theorem lambdaClosed_root (n : ℝ) (hn : -1 ≤ n) :
    lambdaClosed n = 4 * (((1 + n) / 2) ^ (1 / 4 : ℝ)) ^ 3 -
      2 * (((1 + n) / 2) ^ (1 / 4 : ℝ)) ^ 4 - 1 := by
  obtain ⟨hs0, hs⟩ := closed_root n hn
  conv_lhs => rw [hs]
  exact lambdaClosed_param _ hs0

theorem lambdaClosed_bounds (n : ℝ) (hn : n ∈ Icc (-7 / 8 : ℝ) 1) :
    -5 / 8 ≤ lambdaClosed n ∧ lambdaClosed n ≤ 1 := by
  obtain ⟨hl, hu⟩ := root_bounds n hn
  rw [lambdaClosed_root n (by linarith [hn.1])]
  set s := ((1 + n) / 2) ^ (1 / 4 : ℝ)
  constructor
  · rcases hl.eq_or_lt with h | h
    · rw [← h]; norm_num
    · have := quartic_strictMono (1 / 2) s (by norm_num) h hu
      norm_num at this ⊢
      linarith
  · rcases hu.eq_or_lt with h | h
    · rw [h]; norm_num
    · have := quartic_strictMono s 1 (by linarith) h le_rfl
      norm_num at this ⊢
      linarith

theorem Lambda_param_value (n : ℝ) (hn : n ∈ Ioo (-1 : ℝ) (-7 / 8)) :
    Lambda n ∈ Ioo (-1 : ℝ) (-5 / 8) := by
  rw [Lambda_param_branch n hn]
  obtain ⟨h1, h2⟩ := lambdaParameter_open n hn
  exact nuB_open _ h1 h2

/-- `Λ` is strictly increasing on `[-1,1]`. -/
theorem Lambda_strictMonoOn : StrictMonoOn Lambda (Icc (-1 : ℝ) 1) := by
  intro x hx y hy hxy
  by_cases hx1 : x ≤ -1
  · have hxe : x = -1 := le_antisymm hx1 hx.1
    subst hxe
    rw [Lambda_neg_one]
    by_cases hy2 : y < -7 / 8
    · exact (Lambda_param_value y ⟨hxy, hy2⟩).1
    · rw [Lambda_closed_branch y (not_lt.mp hy2)]
      linarith [(lambdaClosed_bounds y ⟨not_lt.mp hy2, hy.2⟩).1]
  · have hx1' : -1 < x := lt_of_not_ge hx1
    by_cases hx2 : x < -7 / 8
    · by_cases hy2 : y < -7 / 8
      · rw [Lambda_param_branch x ⟨hx1', hx2⟩, Lambda_param_branch y ⟨by linarith, hy2⟩]
        obtain ⟨hax, hvx⟩ := lambdaParameter_spec x ⟨hx1'.le, hx2.le⟩
        obtain ⟨hay, hvy⟩ := lambdaParameter_spec y ⟨by linarith, hy2.le⟩
        have hlt : (lambdaParameter y : ℝ) < lambdaParameter x := by
          by_contra h
          push Not at h
          have := transposeParam_strictAnti.antitoneOn ⟨hax, (lambdaParameter x).property.2⟩
            ⟨hay, (lambdaParameter y).property.2⟩ h
          rw [hvx, hvy] at this
          linarith
        exact nuB_strictAnti ⟨hay, (lambdaParameter y).property.2⟩
          ⟨hax, (lambdaParameter x).property.2⟩ hlt
      · have h1 := (Lambda_param_value x ⟨hx1', hx2⟩).2
        rw [Lambda_closed_branch y (not_lt.mp hy2)]
        linarith [(lambdaClosed_bounds y ⟨not_lt.mp hy2, hy.2⟩).1]
    · have hx2' : -7 / 8 ≤ x := not_lt.mp hx2
      rw [Lambda_closed_branch x hx2', Lambda_closed_branch y (by linarith),
        lambdaClosed_root x (by linarith), lambdaClosed_root y (by linarith)]
      obtain ⟨hlx, _⟩ := root_bounds x ⟨hx2', hx.2⟩
      obtain ⟨_, huy⟩ := root_bounds y ⟨by linarith, hy.2⟩
      have hsx := (closed_root x (by linarith)).1
      have hlt : ((1 + x) / 2) ^ (1 / 4 : ℝ) < ((1 + y) / 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_lt_rpow (by linarith) (by linarith) (by norm_num)
      have := quartic_strictMono _ _ hsx hlt huy
      linarith

theorem Lambda_ge_self (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) : x ≤ Lambda x := by
  by_cases hx1 : x ≤ -1
  · have hxe : x = -1 := le_antisymm hx1 hx.1
    subst hxe
    rw [Lambda_neg_one]
  · have hx1' : -1 < x := lt_of_not_ge hx1
    by_cases hx2 : x < -7 / 8
    · rw [Lambda_param_branch x ⟨hx1', hx2⟩]
      obtain ⟨ha, hv⟩ := lambdaParameter_spec x ⟨hx1'.le, hx2.le⟩
      obtain ⟨hl, hu⟩ := lambdaParameter_open x ⟨hx1', hx2⟩
      have hgap := (randomGap_bounds _ ⟨hl, hu⟩).1
      have h0 : (lambdaParameter x : ℝ) ≠ 0 := by linarith
      rw [transposeParam_eq _ h0] at hv
      unfold randomGap at hgap
      linarith
    · have hx2' : -7 / 8 ≤ x := not_lt.mp hx2
      rw [Lambda_closed_branch x hx2', lambdaClosed_root x (by linarith)]
      obtain ⟨hs0, hs⟩ := closed_root x (by linarith)
      obtain ⟨_, hu⟩ := root_bounds x ⟨hx2', hx.2⟩
      set s := ((1 + x) / 2) ^ (1 / 4 : ℝ)
      have h3 : 0 ≤ s ^ 3 := pow_nonneg hs0 3
      have : 0 ≤ 4 * s ^ 3 * (1 - s) := by
        have : 0 ≤ 1 - s := by linarith
        positivity
      nlinarith

theorem Lambda_mapsTo : MapsTo Lambda (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  intro x hx
  refine ⟨le_trans hx.1 (Lambda_ge_self x hx), ?_⟩
  by_cases hx1 : x ≤ -1
  · rw [le_antisymm hx1 hx.1, Lambda_neg_one]; norm_num
  · by_cases hx2 : x < -7 / 8
    · linarith [(Lambda_param_value x ⟨lt_of_not_ge hx1, hx2⟩).2]
    · rw [Lambda_closed_branch x (not_lt.mp hx2)]
      exact (lambdaClosed_bounds x ⟨not_lt.mp hx2, hx.2⟩).2

theorem Lambda_surjOn : SurjOn Lambda (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  intro m hm
  by_cases hm1 : m ≤ -1
  · refine ⟨-1, by norm_num, ?_⟩
    rw [Lambda_neg_one]; linarith [hm.1]
  · have hm1' : -1 < m := lt_of_not_ge hm1
    by_cases hm2 : m < -5 / 8
    · -- randomized branch: solve `nuB a = m`
      have hc : Continuous (fun t : I => -nuB ((1 + (t : ℝ)) / 2)) := by
        apply continuous_iff_continuousAt.mpr
        intro t
        have ht : 0 < 1 + (t : ℝ) := by linarith [t.property.1]
        unfold nuB
        fun_prop (disch := positivity)
      obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := -m)
        (by norm_num [nuB]; linarith) (by norm_num [nuB]; linarith)
      let a : I := ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩
      have hv : nuB a = m := by change nuB ((1 + (t : ℝ)) / 2) = m; linarith
      have hal : (1 / 2 : ℝ) < a := by
        rcases (show (1 / 2 : ℝ) ≤ a by dsimp [a]; linarith [t.property.1]).eq_or_lt with h | h
        · rw [← h, nuB_endpoints.1] at hv; linarith
        · exact h
      have hau : (a : ℝ) < 1 := by
        rcases a.property.2.eq_or_lt with h | h
        · rw [h, nuB_endpoints.2] at hv; linarith
        · exact h
      have hn := transposeParam_open a hal hau
      refine ⟨transposeParam a, ⟨hn.1.le, by linarith [hn.2]⟩, ?_⟩
      rw [Lambda_param_branch _ hn, lambdaParameter_value a hal.le, hv]
    · -- closed branch: solve `4 s^3 - 2 s^4 - 1 = m` with `s ∈ [1/2,1]`
      have hc : Continuous (fun t : I =>
          4 * ((1 + (t : ℝ)) / 2) ^ 3 - 2 * ((1 + (t : ℝ)) / 2) ^ 4 - 1) := by fun_prop
      obtain ⟨t, ht⟩ := Verification.exists_unitInterval_eq hc (z := m)
        (by norm_num; linarith) (by norm_num; linarith [hm.2])
      set s := (1 + (t : ℝ)) / 2 with hsdef
      have hs0 : 0 ≤ s := by rw [hsdef]; linarith [t.property.1]
      have hs1 : 1 / 2 ≤ s := by rw [hsdef]; linarith [t.property.1]
      have hs2 : s ≤ 1 := by rw [hsdef]; linarith [t.property.2]
      have hn1 : -7 / 8 ≤ 2 * s ^ 4 - 1 := by
        have : (1 / 2 : ℝ) ^ 4 ≤ s ^ 4 := pow_le_pow_left₀ (by norm_num) hs1 4
        linarith
      have hn2 : 2 * s ^ 4 - 1 ≤ 1 := by
        have : s ^ 4 ≤ (1 : ℝ) ^ 4 := pow_le_pow_left₀ hs0 hs2 4
        linarith
      refine ⟨2 * s ^ 4 - 1, ⟨by linarith, hn2⟩, ?_⟩
      rw [Lambda_closed_branch _ hn1, lambdaClosed_param s hs0]
      exact ht

/-- `Λ` is a strictly increasing bijection of `[-1,1]`. -/
theorem Lambda_bijOn : BijOn Lambda (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) :=
  ⟨Lambda_mapsTo, Lambda_strictMonoOn.injOn, Lambda_surjOn⟩

/-- Both displayed formulas give `Λ(-7/8) = -5/8`. -/
theorem Lambda_junction :
    Lambda (-7 / 8) = -5 / 8 ∧ transposeParam (1 / 2) = -7 / 8 ∧ nuB (1 / 2) = -5 / 8 := by
  refine ⟨?_, transposeParam_endpoints.1, nuB_endpoints.1⟩
  rw [Lambda_closed_branch _ le_rfl]
  have h := lambdaClosed_param (1 / 2) (by norm_num)
  norm_num at h ⊢
  linarith

#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_eq
#assert_standard_axioms Papers.Rockel2026ExactBlest.nu_transpose_familyB_param
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_factor
#assert_standard_axioms Papers.Rockel2026ExactBlest.nuB_factor
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_strictAnti
#assert_standard_axioms Papers.Rockel2026ExactBlest.nuB_strictAnti
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_endpoints
#assert_standard_axioms Papers.Rockel2026ExactBlest.nuB_endpoints
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_open
#assert_standard_axioms Papers.Rockel2026ExactBlest.nuB_open
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_range
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_exists_unique
#assert_standard_axioms Papers.Rockel2026ExactBlest.transposeParam_bijOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.lambdaParameter_spec
#assert_standard_axioms Papers.Rockel2026ExactBlest.lambdaParameter_value
#assert_standard_axioms Papers.Rockel2026ExactBlest.lambdaParameter_open
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_neg_one
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_param_branch
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_closed_branch
#assert_standard_axioms Papers.Rockel2026ExactBlest.rpow_fourth_three_quarters
#assert_standard_axioms Papers.Rockel2026ExactBlest.fourthRoot_pow
#assert_standard_axioms Papers.Rockel2026ExactBlest.lambdaClosed_param
#assert_standard_axioms Papers.Rockel2026ExactBlest.closed_root
#assert_standard_axioms Papers.Rockel2026ExactBlest.quartic_strictMono
#assert_standard_axioms Papers.Rockel2026ExactBlest.root_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.lambdaClosed_root
#assert_standard_axioms Papers.Rockel2026ExactBlest.lambdaClosed_bounds
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_param_value
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_strictMonoOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_ge_self
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_mapsTo
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_surjOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_bijOn
#assert_standard_axioms Papers.Rockel2026ExactBlest.Lambda_junction

end
end Papers.Rockel2026ExactBlest
