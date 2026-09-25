import Copula.Families.Nelsen
import Copula.Order.Orthant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Lower-orthant parameter order of the Genest–Ghoudi family (Nelsen 15)

With `φ_c(t)=(1-t^{1/c})^c` and `ψ_c(x)=((1-x^{1/c})₊)^c`, the copula is
`ψ_c(φ_c(u)+φ_c(v))`. For `θ≤η` the generator ratio `φ_θ/φ_η` is nondecreasing on `(0,1)`
(its logarithmic derivative is `z/(1-z)` evaluated at two ordered powers of `t`), and
`φ_η ≤ φ_θ`. The classical ratio argument (Nelsen, Corollary 4.4.6) then gives
`C_θ ≤ C_η` pointwise.
-/

open Set Real ProbabilityTheory Copula
open scoped unitInterval

namespace Verification.GenestGhoudiOrder

/-- The generator `φ_c(t)=(1-t^{1/c})^c`. -/
noncomputable def phi (c t : ℝ) : ℝ := (1 - t ^ c⁻¹) ^ c

/-- The inverse generator `ψ_c(x)=((1-x^{1/c})₊)^c`. -/
noncomputable def psi (c x : ℝ) : ℝ := (max 0 (1 - x ^ c⁻¹)) ^ c

variable {c : ℝ}

theorem one_sub_rpow_nonneg (hc : 1 ≤ c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ 1 - t ^ c⁻¹ := by
  have := rpow_le_one ht0 ht1 (inv_nonneg.mpr (by linarith : (0:ℝ) ≤ c))
  linarith

theorem phi_nonneg (hc : 1 ≤ c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ phi c t :=
  rpow_nonneg (one_sub_rpow_nonneg hc ht0 ht1) c

theorem phi_one (hc : 1 ≤ c) : phi c 1 = 0 := by
  simp [phi, zero_rpow (by linarith : c ≠ 0)]

theorem psi_phi (hc : 1 ≤ c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : psi c (phi c t) = t := by
  have hc0 : 0 < c := by linarith
  have h1 := one_sub_rpow_nonneg hc ht0 ht1
  unfold psi phi
  rw [← rpow_mul h1, mul_inv_cancel₀ hc0.ne', rpow_one, sub_sub_cancel,
    max_eq_right (rpow_nonneg ht0 _), ← rpow_mul ht0, inv_mul_cancel₀ hc0.ne', rpow_one]

theorem phi_psi (hc : 1 ≤ c) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : phi c (psi c x) = x := by
  have hc0 : 0 < c := by linarith
  have h1 := one_sub_rpow_nonneg hc hx0 hx1
  unfold psi phi
  rw [max_eq_right h1, ← rpow_mul h1, mul_inv_cancel₀ hc0.ne', rpow_one, sub_sub_cancel,
    ← rpow_mul hx0, inv_mul_cancel₀ hc0.ne', rpow_one]

theorem psi_antitone (hc : 1 ≤ c) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    psi c y ≤ psi c x := by
  have hc0 : 0 < c := by linarith
  unfold psi
  apply rpow_le_rpow (le_max_left _ _) _ hc0.le
  apply max_le_max le_rfl
  have := rpow_le_rpow hx hxy (inv_nonneg.mpr hc0.le)
  linarith

theorem psi_nonneg (_hc : 1 ≤ c) (x : ℝ) : 0 ≤ psi c x :=
  rpow_nonneg (le_max_left _ _) _

theorem psi_of_one_le (hc : 1 ≤ c) {x : ℝ} (hx : 1 ≤ x) : psi c x = 0 := by
  have hc0 : 0 < c := by linarith
  unfold psi
  have : 1 ≤ x ^ c⁻¹ := one_le_rpow hx (inv_nonneg.mpr hc0.le)
  rw [max_eq_left (by linarith), zero_rpow hc0.ne']

theorem psi_le_one (hc : 1 ≤ c) {x : ℝ} (hx : 0 ≤ x) : psi c x ≤ 1 := by
  have hc0 : 0 < c := by linarith
  unfold psi
  apply rpow_le_one (le_max_left _ _) _ hc0.le
  apply max_le zero_le_one
  have := rpow_nonneg hx c⁻¹
  linarith

/-- `φ_η ≤ φ_θ` for `θ≤η`. -/
theorem phi_le_phi {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    phi η t ≤ phi θ t := by
  have hθ0 : 0 < θ := by linarith
  have hη0 : 0 < η := by linarith
  set p := t ^ η⁻¹
  have hp0 : 0 ≤ p := rpow_nonneg ht0 _
  have hp1 : p ≤ 1 := rpow_le_one ht0 ht1 (inv_nonneg.mpr hη0.le)
  set r := η / θ
  have hr : 1 ≤ r := (one_le_div hθ0).mpr hθη
  have htθ : t ^ θ⁻¹ = p ^ r := by
    rw [← rpow_mul ht0]; congr 1; dsimp [r]; field_simp
  -- `(1-p)^r + p^r ≤ 1`
  have hkey : (1 - p) ^ r ≤ 1 - p ^ r := by
    have h1 : (1 - p) ^ r ≤ 1 - p := rpow_le_self_of_le_one (by linarith) (by linarith) hr
    have h2 : p ^ r ≤ p := rpow_le_self_of_le_one hp0 hp1 hr
    linarith
  unfold phi
  rw [htθ]
  have hq : (1 - p) ^ η = ((1 - p) ^ r) ^ θ := by
    rw [← rpow_mul (by linarith)]; congr 1; dsimp [r]; field_simp
  rw [hq]
  exact rpow_le_rpow (rpow_nonneg (by linarith) _) hkey hθ0.le

/-- The logarithmic generator ratio. -/
noncomputable def logRatio (θ η t : ℝ) : ℝ :=
  θ * log (1 - t ^ θ⁻¹) - η * log (1 - t ^ η⁻¹)

theorem hasDerivAt_logTerm (hc : 1 ≤ c) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun x => c * log (1 - x ^ c⁻¹)) (-(t ^ c⁻¹ / t) / (1 - t ^ c⁻¹)) t := by
  have hc0 : 0 < c := by linarith
  have hlt : t ^ c⁻¹ < 1 := rpow_lt_one ht0.le ht1 (inv_pos.mpr hc0)
  have hd := Real.hasDerivAt_rpow_const (x := t) (p := c⁻¹) (Or.inl ht0.ne')
  have hl := (hd.const_sub 1).log (by linarith)
  convert hl.const_mul c using 1
  rw [rpow_sub_one ht0.ne']
  field_simp

theorem logRatio_monotoneOn {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) :
    MonotoneOn (logRatio θ η) (Ioo 0 1) := by
  have hη : 1 ≤ η := hθ.trans hθη
  have hD : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt (logRatio θ η)
      (-(t ^ θ⁻¹ / t) / (1 - t ^ θ⁻¹) - -(t ^ η⁻¹ / t) / (1 - t ^ η⁻¹)) t := by
    intro t ht
    exact (hasDerivAt_logTerm hθ ht.1 ht.2).sub (hasDerivAt_logTerm hη ht.1 ht.2)
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 1)
  · exact fun t ht => (hD t ht).continuousAt.continuousWithinAt
  · rw [interior_Ioo]; exact fun t ht => (hD t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro t ht
    rw [(hD t ht).deriv]
    have hθ0 : 0 < θ := by linarith
    have hη0 : 0 < η := by linarith
    set A := t ^ η⁻¹
    set B := t ^ θ⁻¹
    have hA1 : A < 1 := rpow_lt_one ht.1.le ht.2 (inv_pos.mpr hη0)
    have hB1 : B < 1 := rpow_lt_one ht.1.le ht.2 (inv_pos.mpr hθ0)
    have hBA : B ≤ A := rpow_le_rpow_of_exponent_ge ht.1 ht.2.le
      (inv_anti₀ hθ0 hθη)
    have ht0 := ht.1
    have hA0 : 1 - A ≠ 0 := by linarith
    have hB0 : 1 - B ≠ 0 := by linarith
    have e : -(B / t) / (1 - B) - -(A / t) / (1 - A) = (A - B) / (t * (1 - A) * (1 - B)) := by
      field_simp
      ring
    rw [e]
    apply div_nonneg (by linarith)
    have : 0 < 1 - A := by linarith
    have : 0 < 1 - B := by linarith
    positivity

/-- The generator ratio `φ_θ/φ_η` is nondecreasing, in cross-multiplied form. -/
theorem phi_ratio {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ht : t ≤ 1) :
    phi θ s * phi η t ≤ phi θ t * phi η s := by
  have hη : 1 ≤ η := hθ.trans hθη
  rcases ht.lt_or_eq with ht1 | ht1
  swap
  · subst ht1; rw [phi_one hθ, phi_one hη]; simp
  have hs1 : s < 1 := hst.trans_lt ht1
  have ht0 : 0 < t := hs.trans_le hst
  have hm := logRatio_monotoneOn hθ hθη ⟨hs, hs1⟩ ⟨ht0, ht1⟩ hst
  have hpos (c x : ℝ) (hc : 1 ≤ c) (hx0 : 0 < x) (hx1 : x < 1) : 0 < 1 - x ^ c⁻¹ := by
    have := rpow_lt_one hx0.le hx1 (inv_pos.mpr (by linarith : (0:ℝ) < c)); linarith
  have hlog (c x : ℝ) (hc : 1 ≤ c) (hx0 : 0 < x) (hx1 : x < 1) :
      log (phi c x) = c * log (1 - x ^ c⁻¹) := by
    unfold phi; rw [log_rpow (hpos c x hc hx0 hx1)]
  have hφ (c x : ℝ) (hc : 1 ≤ c) (hx0 : 0 < x) (hx1 : x < 1) : 0 < phi c x :=
    rpow_pos_of_pos (hpos c x hc hx0 hx1) c
  unfold logRatio at hm
  rw [← hlog θ s hθ hs hs1, ← hlog η s hη hs hs1, ← hlog θ t hθ ht0 ht1,
    ← hlog η t hη ht0 ht1] at hm
  have h1 : log (phi θ s * phi η t) ≤ log (phi θ t * phi η s) := by
    rw [log_mul (hφ θ s hθ hs hs1).ne' (hφ η t hη ht0 ht1).ne',
      log_mul (hφ θ t hθ ht0 ht1).ne' (hφ η s hη hs hs1).ne']
    linarith
  exact (log_le_log_iff (mul_pos (hφ θ s hθ hs hs1) (hφ η t hη ht0 ht1))
    (mul_pos (hφ θ t hθ ht0 ht1) (hφ η s hη hs hs1))).mp h1

/-- The Genest–Ghoudi CDF in generator form. -/
theorem cdf_eq_psi (θ : ℝ) (hθ : 1 ≤ θ) (u v : I) (hu : u ≠ 0) (hv : v ≠ 0) :
    (genestGhoudi θ hθ).cdf ![u, v] = psi θ (phi θ u + phi θ v) := by
  rw [cdf_genestGhoudi θ hθ _ (by intro i; fin_cases i <;> simpa)]
  rfl

/-- Table 3: Genest–Ghoudi increases in lower-orthant order. -/
theorem genestGhoudi_cdf_mono {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) (u v : I) :
    (genestGhoudi θ hθ).cdf ![u, v] ≤ (genestGhoudi η (hθ.trans hθη)).cdf ![u, v] := by
  have hη : 1 ≤ η := hθ.trans hθη
  by_cases hz : u = 0 ∨ v = 0
  · rcases hz with hz | hz
    · rw [(genestGhoudi θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, v] 0 (by simp [hz]),
        (genestGhoudi η hη).cdf_eq_zero_of_coord_eq_zero ![u, v] 0 (by simp [hz])]
    · rw [(genestGhoudi θ hθ).cdf_eq_zero_of_coord_eq_zero ![u, v] 1 (by simp [hz]),
        (genestGhoudi η hη).cdf_eq_zero_of_coord_eq_zero ![u, v] 1 (by simp [hz])]
  push Not at hz
  rw [cdf_eq_psi θ hθ u v hz.1 hz.2, cdf_eq_psi η hη u v hz.1 hz.2]
  have hu0 : 0 ≤ (u : ℝ) := u.2.1
  have hu1 : (u : ℝ) ≤ 1 := u.2.2
  have hv0 : 0 ≤ (v : ℝ) := v.2.1
  have hv1 : (v : ℝ) ≤ 1 := v.2.2
  have hup : 0 < (u : ℝ) := lt_of_le_of_ne hu0 (fun e => hz.1 (Subtype.ext e.symm))
  have hvp : 0 < (v : ℝ) := lt_of_le_of_ne hv0 (fun e => hz.2 (Subtype.ext e.symm))
  set x := phi η u + phi η v
  set y := phi θ u + phi θ v
  have hx0 : 0 ≤ x := add_nonneg (phi_nonneg hη hu0 hu1) (phi_nonneg hη hv0 hv1)
  have hxy : x ≤ y := add_le_add (phi_le_phi hθ hθη hu0 hu1) (phi_le_phi hθ hθη hv0 hv1)
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [psi_of_one_le hθ (hx1.trans hxy), psi_of_one_le hη hx1]
  set w := psi η x
  have hw0 : 0 ≤ w := psi_nonneg hη x
  have hw1 : w ≤ 1 := psi_le_one hη hx0
  have hφw : phi η w = x := phi_psi hη hx0 hx1.le
  rcases hx0.lt_or_eq with hxp | hxe
  swap
  · -- `x=0`: `w=1`
    have : w = 1 := by
      show psi η x = 1
      rw [← hxe]; unfold psi
      rw [zero_rpow (inv_ne_zero (by linarith)), sub_zero, max_eq_right zero_le_one, one_rpow]
    rw [this]
    exact psi_le_one hθ (add_nonneg (phi_nonneg hθ hu0 hu1) (phi_nonneg hθ hv0 hv1))
  have hwpos : 0 < w := by
    by_contra hcon
    have hw : w = 0 := le_antisymm (not_lt.mp hcon) hw0
    rw [hw, show phi η 0 = 1 by simp [phi, zero_rpow (inv_pos.mpr (by linarith : (0:ℝ) < η)).ne']]
      at hφw
    linarith
  have hwu : w ≤ u := by
    have := psi_antitone hη (phi_nonneg hη hu0 hu1)
      (le_add_of_nonneg_right (phi_nonneg hη hv0 hv1) : phi η u ≤ x)
    rwa [psi_phi hη hu0 hu1] at this
  have hwv : w ≤ v := by
    have := psi_antitone hη (phi_nonneg hη hv0 hv1)
      (le_add_of_nonneg_left (phi_nonneg hη hu0 hu1) : phi η v ≤ x)
    rwa [psi_phi hη hv0 hv1] at this
  have h1 := phi_ratio hθ hθη hwpos hwu hu1
  have h2 := phi_ratio hθ hθη hwpos hwv hv1
  rw [hφw] at h1 h2
  have hle : phi θ w ≤ y := by
    have : phi θ w * x ≤ y * x := by
      have := add_le_add h1 h2
      simp only [y]
      nlinarith
    exact le_of_mul_le_mul_right this hxp
  calc psi θ y ≤ psi θ (phi θ w) := psi_antitone hθ (phi_nonneg hθ hw0 hw1) hle
    _ = w := psi_phi hθ hw0 hw1

theorem genestGhoudi_lowerOrthant_mono {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) :
    (genestGhoudi θ hθ).LowerOrthantLE (genestGhoudi η (hθ.trans hθη)) := by
  intro x
  have hx : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
  rw [hx]
  exact genestGhoudi_cdf_mono hθ hθη _ _

end Verification.GenestGhoudiOrder
