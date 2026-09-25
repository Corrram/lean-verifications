import Verification.Nelsen18
import Verification.ConditionalEnergy
import Copula.Order.Schur
import Copula.Rank.ConditionalDerivative
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-! # Nelsen 18 is not Schur-increasing in its parameter

At threshold `v=1/9`, with `q=θ/(u-1)`, `S=e^q+e^{θ/(v-1)}`, `L=log S` and `p=e^q/S`,
the conditional CDF on the positive region `L<-θ` equals
`e^q q²/(S L²)=p(1+(-log p)/(-L))²`. For `θ=4` this is at most
`p(1-log p/4)² ≤ (2/5)(1+log(5/2)/4)² ≤ 5/8`, because `p<1-e^{-1/2}≤2/5`.
For `θ=2`, at the point with `e^q=e^{-9/4}/4` (so `p=1/5`) it is
`(9/4+2log 2)²/(5(9/4-log(5/4))²)>5/8`. The convex test `z ↦ (z-5/8)₊` therefore
separates the two conditional CDFs, so `C₂ ≤_∂S C₄` fails.
-/

open MeasureTheory ProbabilityTheory Set Filter Real Copula
open scoped unitInterval Topology

namespace Verification.N18Schur

noncomputable def S (θ K x : ℝ) : ℝ := exp (θ / (x - 1)) + K
noncomputable def F (θ K x : ℝ) : ℝ := 1 + θ / log (S θ K x)
noncomputable def G (θ K x : ℝ) : ℝ :=
  θ ^ 2 * exp (θ / (x - 1)) / ((x - 1) ^ 2 * S θ K x * log (S θ K x) ^ 2)

theorem S_pos {θ K : ℝ} (hK : 0 < K) (x : ℝ) : 0 < S θ K x := by
  unfold S; positivity

theorem continuousAt_S {θ K x : ℝ} (hx : x ≠ 1) : ContinuousAt (S θ K) x := by
  unfold S
  apply ContinuousAt.add _ continuousAt_const
  exact continuous_exp.continuousAt.comp
    (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hx))

theorem hasDerivAt_F {θ K x : ℝ} (hK : 0 < K) (hx : x ≠ 1) (hL : log (S θ K x) ≠ 0) :
    HasDerivAt (F θ K) (G θ K x) x := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hq : HasDerivAt (fun y : ℝ => θ / (y - 1)) (-θ / (x - 1) ^ 2) x := by
    have := ((hasDerivAt_id x).sub_const 1).inv hx1
    convert this.const_mul θ using 1
    · funext y; simp [div_eq_mul_inv]
    · simp only [id]; field_simp
  have hS : HasDerivAt (S θ K) (exp (θ / (x - 1)) * (-θ / (x - 1) ^ 2)) x := by
    show HasDerivAt (fun y => exp (θ / (y - 1)) + K) _ x
    exact hq.exp.add_const K
  have hLd := hS.log (S_pos hK x).ne'
  have hD := (hLd.inv hL).const_mul θ
  unfold F G
  convert hD.const_add 1 using 1
  · funext y; simp [div_eq_mul_inv]
  · have := S_pos (θ := θ) hK x
    field_simp

/-- The CDF section on `(0,1)` for a threshold below one. -/
theorem cdfSection_eq (θ : ℝ) (hθ : 2 ≤ θ) (v : I) (hv : (v : ℝ) < 1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    cdfSection (nelsen18 θ hθ) v x = max 0 (F θ (exp (θ / ((v : ℝ) - 1))) x) := by
  dsimp only [cdfSection]
  have hu1 : (⟨x, hx.1.le, hx.2.le⟩ : I) < 1 := by
    rw [← Subtype.coe_lt_coe]; simpa using hx.2
  rw [projIcc_of_mem zero_le_one ⟨hx.1.le, hx.2.le⟩,
    nelsen18_cdf_of_lt_one θ hθ _ _ hu1 (by rw [← Subtype.coe_lt_coe]; simpa using hv)]
  rfl

/-- On the positive region the CDF section is differentiable with derivative `G`. -/
theorem hasDerivAt_cdfSection_pos (θ : ℝ) (hθ : 2 ≤ θ) (v : I) (hv : (v : ℝ) < 1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hL : log (S θ (exp (θ / ((v : ℝ) - 1))) x) < -θ) :
    HasDerivAt (cdfSection (nelsen18 θ hθ) v) (G θ (exp (θ / ((v : ℝ) - 1))) x) x := by
  set K := exp (θ / ((v : ℝ) - 1))
  have hK : 0 < K := exp_pos _
  have hθ0 : 0 < θ := by linarith
  have hx1 : x ≠ 1 := hx.2.ne
  have hLc : ContinuousAt (fun y => log (S θ K y)) x :=
    (continuousAt_log (S_pos hK x).ne').comp (continuousAt_S hx1)
  have hev : ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 ∧ log (S θ K y) < -θ :=
    (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hx.1 hx.2).and
      (hLc.eventually (gt_mem_nhds hL))
  apply (hasDerivAt_F hK hx1 (by linarith)).congr_of_eventuallyEq
  filter_upwards [hev] with y hy
  rw [cdfSection_eq θ hθ v hv hy.1]
  apply max_eq_right
  unfold F
  have hneg : log (S θ K y) < 0 := by linarith
  have : -1 ≤ θ / log (S θ K y) := by
    rw [le_div_iff_of_neg hneg]; linarith
  linarith

/-- On the zero region the CDF section is locally zero. -/
theorem hasDerivAt_cdfSection_zero (θ : ℝ) (hθ : 2 ≤ θ) (v : I) (hv : (v : ℝ) < 1) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hL : -θ < log (S θ (exp (θ / ((v : ℝ) - 1))) x)) :
    HasDerivAt (cdfSection (nelsen18 θ hθ) v) 0 x := by
  set K := exp (θ / ((v : ℝ) - 1))
  have hK : 0 < K := exp_pos _
  have hθ0 : 0 < θ := by linarith
  have hx1 : x ≠ 1 := hx.2.ne
  have hLc : ContinuousAt (fun y => log (S θ K y)) x :=
    (continuousAt_log (S_pos hK x).ne').comp (continuousAt_S hx1)
  have hev : ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 ∧ -θ < log (S θ K y) :=
    (show ∀ᶠ y in 𝓝 x, y ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds hx.1 hx.2).and
      (hLc.eventually (lt_mem_nhds hL))
  apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [hev] with y hy
  rw [cdfSection_eq θ hθ v hv hy.1]
  apply max_eq_left
  unfold F
  -- `S<1`, so `log S<0`; then `θ/log S ≤ -1`
  have hS1 : S θ K y < 1 := by
    have h1 : exp (θ / (y - 1)) < 1 / 2 := by
      have hq : θ / (y - 1) ≤ -θ := by
        rw [div_le_iff_of_neg (by linarith [hy.1.2])]; nlinarith [hy.1.1, hy.1.2]
      have h2 : exp (θ / (y - 1)) ≤ exp (-2) :=
        exp_le_exp.mpr (hq.trans (by linarith))
      have h3 : exp (-2 : ℝ) < 1 / 2 := by
        have h4 : exp (-2 : ℝ) * exp 2 = 1 := by rw [← exp_add]; norm_num
        have h5 : (2:ℝ) < exp 2 := by have := add_one_le_exp (2:ℝ); linarith
        nlinarith [exp_pos (-2 : ℝ)]
      linarith
    have h2 : K < 1 / 2 := by
      have hq : θ / ((v : ℝ) - 1) ≤ -θ := by
        rw [div_le_iff_of_neg (by linarith)]; nlinarith [v.2.1]
      have h2 : K ≤ exp (-2) := exp_le_exp.mpr (hq.trans (by linarith))
      have h3 : exp (-2 : ℝ) < 1 / 2 := by
        have h4 : exp (-2 : ℝ) * exp 2 = 1 := by rw [← exp_add]; norm_num
        have h5 : (2:ℝ) < exp 2 := by have := add_one_le_exp (2:ℝ); linarith
        nlinarith [exp_pos (-2 : ℝ)]
      linarith
    unfold S; linarith
  have hneg : log (S θ K y) < 0 := log_neg (S_pos hK y) hS1
  have : θ / log (S θ K y) ≤ -1 := by
    rw [div_le_iff_of_neg hneg]; linarith [hy.2]
  linarith

/-! ## The bound for `θ=4` -/

/-- `h(p)=p(1-log p/4)²` is monotone on `(0,1)`. -/
theorem hmono : MonotoneOn (fun p : ℝ => p * (1 - log p / 4) ^ 2) (Ioo 0 1) := by
  have hD : ∀ p ∈ Ioo (0:ℝ) 1, HasDerivAt (fun p : ℝ => p * (1 - log p / 4) ^ 2)
      ((1 - log p / 4) ^ 2 + p * (2 * (1 - log p / 4) * (-(p⁻¹) / 4))) p := by
    intro p hp
    have hl := (hasDerivAt_log hp.1.ne').div_const 4
    have hk := (hl.const_sub 1).pow 2
    have := (hasDerivAt_id p).mul hk
    convert this using 1
    · funext y; simp only [Pi.mul_apply, Pi.pow_apply, id]
    · simp only [Pi.pow_apply, id]; ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · exact fun p hp => (hD p hp).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; exact fun p hp => (hD p hp).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro p hp
    rw [(hD p hp).deriv]
    have hl : log p < 0 := log_neg hp.1 hp.2
    have hp0 := hp.1
    have e : (1 - log p / 4) ^ 2 + p * (2 * (1 - log p / 4) * (-(p⁻¹) / 4)) =
        (1 - log p / 4) * (1 / 2 - log p / 4) := by
      field_simp; ring
    rw [e]
    apply mul_nonneg <;> linarith

theorem exp_neg_half_ge : (3 / 5 : ℝ) ≤ exp (-(1 / 2)) := by
  have h1 : exp (1 / 2 : ℝ) ≤ 5 / 3 :=
    calc exp (1 / 2 : ℝ) ≤ (2 + 1 / 2) / (2 - 1 / 2) :=
          exp_le_two_add_div_two_sub (by norm_num) (by norm_num)
      _ = 5 / 3 := by norm_num
  rw [exp_neg, le_inv_comm₀ (by norm_num) (exp_pos _), show ((3:ℝ) / 5)⁻¹ = 5 / 3 by norm_num]
  exact h1

theorem log_five_halves_le : log (5 / 2 : ℝ) ≤ 1 := by
  rw [← log_exp 1]
  apply log_le_log (by norm_num)
  have := quadratic_le_exp_of_nonneg (x := 1) zero_le_one
  norm_num at this
  linarith

/-- The `θ=4` conditional CDF at `v=1/9` is at most `5/8` on the positive region. -/
theorem G_four_le {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hL : log (S 4 (exp (-(9 / 2))) x) < -4) :
    G 4 (exp (-(9 / 2))) x ≤ 5 / 8 := by
  set K := exp (-(9 / 2) : ℝ)
  have hK : 0 < K := exp_pos _
  set q := 4 / (x - 1)
  set s := S 4 K x
  set L := log s
  have hs : 0 < s := S_pos hK x
  have hsdef : s = exp q + K := rfl
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx.2.ne
  set p := exp q / s
  have hp0 : 0 < p := div_pos (exp_pos q) hs
  have hps : exp q = p * s := by dsimp [p]; field_simp
  have hp1 : p < 1 := by
    rw [div_lt_one hs, hsdef]; linarith
  -- `q = log p + L`
  have hqL : q = log p + L := by
    rw [← log_exp q, hps, log_mul hp0.ne' hs.ne']
  -- `G = p q²/L²`
  have hG : G 4 K x = p * q ^ 2 / L ^ 2 := by
    have hq2 : (4:ℝ) ^ 2 / (x - 1) ^ 2 = q ^ 2 := by dsimp [q]; field_simp
    have hL0 : L ≠ 0 := by linarith
    show 4 ^ 2 * exp q / ((x - 1) ^ 2 * s * L ^ 2) = p * q ^ 2 / L ^ 2
    rw [hps, ← hq2]
    field_simp
  -- `p < 2/5`
  have hpmax : p ≤ 2 / 5 := by
    have h1 : s < exp (-4) := by
      rw [← exp_log hs]; exact exp_lt_exp.mpr hL
    have h2 : K = s * (1 - p) := by
      dsimp [p]; field_simp; rw [hsdef]; ring
    -- `1-p = K/s > K/e^{-4} = e^{-1/2}`
    have h3 : exp (-(1 / 2) : ℝ) ≤ 1 - p := by
      have hK4 : K = exp (-(1 / 2)) * exp (-4) := by
        dsimp [K]; rw [← exp_add]; norm_num
      have : exp (-(1 / 2)) * exp (-4) ≤ (1 - p) * exp (-4) := by
        rw [← hK4, h2]
        have : 0 ≤ 1 - p := by linarith
        nlinarith
      exact le_of_mul_le_mul_right this (exp_pos _)
    linarith [exp_neg_half_ge]
  -- `q/L ≤ 1 - log p/4`, and `1 ≤ q/L`
  have hLneg : L < 0 := by linarith
  have hlp : log p < 0 := log_neg hp0 hp1
  have hratio : q ^ 2 / L ^ 2 ≤ (1 - log p / 4) ^ 2 := by
    have e : q ^ 2 / L ^ 2 = (1 + log p / L) ^ 2 := by
      rw [hqL, ← div_pow, add_div, div_self hLneg.ne]
      ring
    rw [e]
    have h1 : 0 ≤ log p / L := div_nonneg_of_nonpos hlp.le hLneg.le
    have h2 : log p / L ≤ -log p / 4 := by
      rw [div_le_iff_of_neg hLneg]
      have : -log p / 4 * L ≤ -log p / 4 * (-4) :=
        mul_le_mul_of_nonneg_left hL.le (by linarith)
      linarith
    apply pow_le_pow_left₀ (by linarith)
    linarith
  rw [hG]
  calc p * q ^ 2 / L ^ 2 = p * (q ^ 2 / L ^ 2) := by ring
    _ ≤ p * (1 - log p / 4) ^ 2 := mul_le_mul_of_nonneg_left hratio hp0.le
    _ ≤ (2 / 5) * (1 - log (2 / 5) / 4) ^ 2 :=
        hmono ⟨hp0, hp1⟩ ⟨by norm_num, by norm_num⟩ hpmax
    _ ≤ 5 / 8 := by
        have : log (2 / 5 : ℝ) = -log (5 / 2) := by
          rw [← log_inv]; norm_num
        rw [this]
        have h1 := log_five_halves_le
        have h0 : 0 ≤ log (5 / 2 : ℝ) := log_nonneg (by norm_num)
        nlinarith

/-! ## The witness for `θ=2` -/

/-- The witness point `x* = 1 + 2/q*` with `q* = -9/4 - log 4`. -/
noncomputable def qStar : ℝ := -(9 / 4) - log 4
noncomputable def xStar : ℝ := 1 + 2 / qStar

theorem log_four_bounds : (1.386294 : ℝ) < log 4 ∧ log 4 < 1.3863 := by
  have h : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; norm_num
  have hl : (0.693147 : ℝ) < log 2 := by
    rw [lt_log_iff_exp_lt (by norm_num)]
    calc exp (0.693147 : ℝ) ≤ _ := exp_bound' (by norm_num) (by norm_num) (n := 10) (by norm_num)
      _ < 2 := by norm_num [Finset.sum_range_succ, Nat.factorial]
  have hu : log 2 < (0.69315 : ℝ) := by
    rw [log_lt_iff_lt_exp (by norm_num)]
    calc (2 : ℝ) < ∑ i ∈ Finset.range 10, (0.69315 : ℝ) ^ i / (Nat.factorial i) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ exp 0.69315 := sum_le_exp_of_nonneg (by norm_num) 10
  rw [h]
  constructor <;> linarith

theorem qStar_lt : qStar < -3 := by
  unfold qStar; linarith [log_four_bounds.1]

theorem xStar_mem : xStar ∈ Ioo (0 : ℝ) 1 := by
  have hq := qStar_lt
  have hq0 : qStar < 0 := by linarith
  unfold xStar
  constructor
  · have : -1 < 2 / qStar := by
      rw [lt_div_iff_of_neg hq0]; linarith
    linarith
  · have : 2 / qStar < 0 := div_neg_of_pos_of_neg (by norm_num) hq0
    linarith

theorem xStar_q : 2 / (xStar - 1) = qStar := by
  have hq0 : qStar ≠ 0 := by linarith [qStar_lt]
  unfold xStar; field_simp; ring

theorem S_xStar : S 2 (exp (-(9 / 4))) xStar = 5 / 4 * exp (-(9 / 4)) := by
  unfold S
  rw [xStar_q, qStar, sub_eq_add_neg, exp_add, exp_neg (log 4), exp_log (by norm_num)]
  ring

theorem log_S_xStar : log (S 2 (exp (-(9 / 4))) xStar) = log (5 / 4) - 9 / 4 := by
  rw [S_xStar, log_mul (by norm_num) (exp_pos _).ne', log_exp]; ring

theorem log_five_fourths_bounds : (1 / 5 : ℝ) ≤ log (5 / 4) ∧ log (5 / 4 : ℝ) < 1 / 4 := by
  constructor
  · have := one_sub_inv_le_log_of_pos (show (0:ℝ) < 5 / 4 by norm_num)
    norm_num at this ⊢; linarith
  · have := log_lt_sub_one_of_pos (show (0:ℝ) < 5 / 4 by norm_num) (by norm_num)
    linarith

theorem log_S_xStar_lt : log (S 2 (exp (-(9 / 4))) xStar) < -2 := by
  rw [log_S_xStar]; linarith [log_five_fourths_bounds.2]

theorem G_xStar_gt : 5 / 8 < G 2 (exp (-(9 / 4))) xStar := by
  have hx1 : xStar - 1 ≠ 0 := sub_ne_zero.mpr xStar_mem.2.ne
  have hG : G 2 (exp (-(9 / 4))) xStar = exp qStar * qStar ^ 2 /
      (S 2 (exp (-(9 / 4))) xStar * log (S 2 (exp (-(9 / 4))) xStar) ^ 2) := by
    unfold G
    rw [← xStar_q]
    field_simp
  rw [hG, log_S_xStar, S_xStar]
  have hE : exp qStar = exp (-(9 / 4)) / 4 := by
    unfold qStar; rw [sub_eq_add_neg, exp_add, exp_neg (log 4), exp_log (by norm_num)]; ring
  have hK : 0 < exp (-(9 / 4) : ℝ) := exp_pos _
  rw [hE]
  generalize exp (-(9 / 4) : ℝ) = K at *
  obtain ⟨hl1, hl2⟩ := log_five_fourths_bounds
  have hq := log_four_bounds
  have hL' : 9 / 4 - log (5 / 4 : ℝ) ≤ 2.05 := by linarith
  have hQ : 3.636294 < -qStar := by unfold qStar; linarith
  have hne : log (5 / 4 : ℝ) - 9 / 4 ≠ 0 := by linarith
  have e : K / 4 * qStar ^ 2 / (5 / 4 * K * (log (5 / 4) - 9 / 4) ^ 2) =
      qStar ^ 2 / (5 * (9 / 4 - log (5 / 4)) ^ 2) := by
    field_simp; ring
  have hpos : 0 < 9 / 4 - log (5 / 4 : ℝ) := by linarith
  rw [e, lt_div_iff₀ (by positivity)]
  have h1 : (9 / 4 - log (5 / 4 : ℝ)) ^ 2 ≤ 2.05 ^ 2 := pow_le_pow_left₀ (by linarith) hL' 2
  have h2 : (3.636294 : ℝ) ^ 2 < qStar ^ 2 := by nlinarith
  norm_num at h1 h2 ⊢
  linarith

/-! ## The separation -/

/-- The threshold `v=1/9`. -/
noncomputable def v9 : I := ⟨1 / 9, by norm_num, by norm_num⟩

theorem v9_exp (θ : ℝ) : θ / ((v9 : ℝ) - 1) = -(9 * θ / 8) := by
  simp only [v9]; field_simp; ring

theorem hinge_convex : ConvexOn ℝ (Icc 0 1) (fun z : ℝ => max (z - 5 / 8) 0) := by
  have h1 : ConvexOn ℝ (Icc (0:ℝ) 1) (fun z : ℝ => z - 5 / 8) :=
    (convexOn_id (convex_Icc 0 1)).sub (concaveOn_const _ (convex_Icc 0 1))
  exact h1.sup (convexOn_const 0 (convex_Icc 0 1))

theorem hinge_continuous : Continuous (fun z : ℝ => max (z - 5 / 8) 0) := by
  fun_prop

/-- For `θ=4`, the conditional CDF at `v=1/9` is at most `5/8` almost everywhere. -/
theorem four_ae_le :
    ∀ᵐ u : I, (nelsen18 4 (by norm_num)).conditionalCDF u v9 ≤ 5 / 8 := by
  set K := exp (-(9 / 2) : ℝ)
  have hK : 0 < K := exp_pos _
  have hvK : exp ((4:ℝ) / ((v9 : ℝ) - 1)) = K := by
    rw [v9_exp]; dsimp [K]; norm_num
  have hv1 : ((v9 : I) : ℝ) < 1 := by simp [v9]; norm_num
  have h0 : ∀ᵐ u : I, u ≠ 0 := by simp [ae_iff]
  have h1 : ∀ᵐ u : I, u ≠ 1 := by simp [ae_iff]
  -- at most one boundary point
  have hb : ∀ᵐ u : I, log (S 4 K u) ≠ -4 := by
    by_cases hex : ∃ u0 : I, log (S 4 K u0) = -4 ∧ (u0 : ℝ) < 1
    · obtain ⟨u0, hu0, hu01⟩ := hex
      have hs : ∀ᵐ u : I, u ≠ u0 := by simp [ae_iff]
      filter_upwards [hs, h1] with u hu hu1 he
      apply hu
      have hu1' : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 (fun e => hu1 (Subtype.ext e))
      have hSu : S 4 K u = S 4 K u0 := by
        have := congrArg exp (he.trans hu0.symm)
        rwa [exp_log (S_pos hK _), exp_log (S_pos hK _)] at this
      unfold S at hSu
      have he2 : (4:ℝ) / ((u : ℝ) - 1) = 4 / ((u0 : ℝ) - 1) :=
        exp_injective (by linarith)
      have hne1 : (u : ℝ) - 1 ≠ 0 := by linarith
      have hne2 : (u0 : ℝ) - 1 ≠ 0 := by linarith
      field_simp at he2
      exact Subtype.ext (by linarith)
    · push Not at hex
      filter_upwards [h1] with u hu1 he
      have hu1' : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 (fun e => hu1 (Subtype.ext e))
      exact absurd hu1' (not_lt.mpr (hex u he))
  filter_upwards [(nelsen18 4 (by norm_num)).conditionalCDF_eq_deriv v9, h0, h1, hb]
    with u hu hu0 hu1 hbd
  rw [hu]
  have hx : (u : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne u.2.1 (fun e => hu0 (Subtype.ext e.symm)),
      lt_of_le_of_ne u.2.2 (fun e => hu1 (Subtype.ext e))⟩
  rcases lt_or_gt_of_ne hbd with hlt | hgt
  · have hd := hasDerivAt_cdfSection_pos 4 (by norm_num) v9 hv1 hx (by rw [hvK]; exact hlt)
    rw [hd.deriv, hvK]
    exact G_four_le hx hlt
  · have hd := hasDerivAt_cdfSection_zero 4 (by norm_num) v9 hv1 hx (by rw [hvK]; exact hgt)
    rw [hd.deriv]; norm_num

/-- Nelsen 18 is not increasing in the directional Schur order: `C₂ ≤_∂S C₄` fails. -/
theorem nelsen18_two_not_schurLE_four :
    ¬ (nelsen18 2 le_rfl).SchurLE (nelsen18 4 (by norm_num)) := by
  intro h
  let φ : ℝ → ℝ := fun z => max (z - 5 / 8) 0
  have hi := h v9 φ hinge_continuous hinge_convex
  -- the right side vanishes
  have hD : (∫ u : I, φ ((nelsen18 4 (by norm_num)).conditionalCDF u v9)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [four_ae_le] with u hu
    simp only [φ, Pi.zero_apply]
    exact max_eq_right (by linarith)
  rw [hD] at hi
  set C := nelsen18 2 le_rfl
  have hnon (u : I) : 0 ≤ φ (C.conditionalCDF u v9) := le_max_right _ _
  have hz := le_antisymm hi (integral_nonneg hnon)
  have ha := (integral_eq_zero_iff_of_nonneg hnon
    (C.integrable_comp_conditionalCDF v9 hinge_continuous)).mp hz
  set K := exp (-(9 / 4) : ℝ)
  have hvK : exp ((2:ℝ) / ((v9 : ℝ) - 1)) = K := by
    rw [v9_exp]; dsimp [K]; norm_num
  have hv1 : ((v9 : I) : ℝ) < 1 := by simp [v9]; norm_num
  let g : I → ℝ := fun u => G 2 K u
  let q : I := ⟨xStar, xStar_mem.1.le, xStar_mem.2.le⟩
  have hK : 0 < K := exp_pos _
  -- continuity of `G` at `x*`
  have hx1 : xStar ≠ 1 := xStar_mem.2.ne
  have hLc : ContinuousAt (fun y => log (S 2 K y)) xStar :=
    (continuousAt_log (S_pos hK _).ne').comp (continuousAt_S hx1)
  have hGc : ContinuousAt (G 2 K) xStar := by
    unfold G
    have hL0 : log (S 2 K xStar) ≠ 0 := by linarith [log_S_xStar_lt]
    have hS0 := S_pos (θ := 2) hK xStar
    have he : ContinuousAt (fun y : ℝ => exp (2 / (y - 1))) xStar :=
      continuous_exp.continuousAt.comp
        (continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hx1))
    apply ContinuousAt.div (continuousAt_const.mul he)
      ((((continuousAt_id.sub continuousAt_const).pow 2).mul (continuousAt_S hx1)).mul
        (hLc.pow 2))
    have : xStar - 1 ≠ 0 := sub_ne_zero.mpr hx1
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ this) hS0.ne') (pow_ne_zero _ hL0)
  have hg : ContinuousAt g q :=
    ContinuousAt.comp (g := G 2 K) (x := q) hGc continuous_subtype_val.continuousAt
  -- local derivative near `x*`
  have hev : ∀ᶠ u : I in 𝓝 q, (u : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ log (S 2 K u) < -2 := by
    have h1 : ∀ᶠ y in 𝓝 xStar, y ∈ Ioo (0 : ℝ) 1 ∧ log (S 2 K y) < -2 :=
      (show ∀ᶠ y in 𝓝 xStar, y ∈ Ioo (0 : ℝ) 1 from Ioo_mem_nhds xStar_mem.1 xStar_mem.2).and
        (hLc.eventually (gt_mem_nhds log_S_xStar_lt))
    exact Filter.Tendsto.eventually (continuous_subtype_val.continuousAt (x := q)) h1
  have hb : ∀ᵐ u : I, u ∈ {u : I | (u : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ log (S 2 K u) < -2} →
      0 ≤ 5 / 8 - g u := by
    filter_upwards [ha, C.conditionalCDF_eq_deriv v9] with u hu heq hmem
    have hd := hasDerivAt_cdfSection_pos 2 le_rfl v9 hv1 hmem.1 (by rw [hvK]; exact hmem.2)
    rw [hvK] at hd
    simp only [Pi.zero_apply, φ] at hu
    rw [heq, hd.deriv] at hu
    have := le_max_left (G 2 K u - 5 / 8) 0
    simp only [g]
    linarith
  have hc := continuousAt_nonneg_of_ae_imp (μ := (volume : Measure I))
    (continuousAt_const.sub hg) hev hb
  have := G_xStar_gt
  change 0 ≤ 5 / 8 - G 2 K xStar at hc
  change 5 / 8 < G 2 K xStar at this
  linarith

theorem nelsen18_not_schur_monotone :
    ¬ (∀ (θ η : ℝ) (hθ : 2 ≤ θ) (hθη : θ ≤ η),
      (nelsen18 θ hθ).SchurLE (nelsen18 η (hθ.trans hθη))) := by
  intro h
  exact nelsen18_two_not_schurLE_four (h 2 4 le_rfl (by norm_num))

end Verification.N18Schur
