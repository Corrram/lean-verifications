import Verification.FootruleJensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Exact evaluation of the relaxed xi-footrule coefficients -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

private theorem integral_three_pieces (f g₀ g₁ g₂ : ℝ → ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (h₀ : EqOn f g₀ (Ioo 0 a)) (h₁ : EqOn f g₁ (Ioo a b))
    (h₂ : EqOn f g₂ (Ioo b 1))
    (hi₀ : IntervalIntegrable g₀ volume 0 a)
    (hi₁ : IntervalIntegrable g₁ volume a b)
    (hi₂ : IntervalIntegrable g₂ volume b 1) :
    (∫ v in (0 : ℝ)..1, f v) = (∫ v in (0 : ℝ)..a, g₀ v) +
      (∫ v in a..b, g₁ v) + ∫ v in b..1, g₂ v := by
  have hf₀ := hi₀.congr_uIoo (by simpa only [uIoo_of_le ha] using h₀.symm)
  have hf₁ := hi₁.congr_uIoo (by simpa only [uIoo_of_le hab] using h₁.symm)
  have hf₂ := hi₂.congr_uIoo (by simpa only [uIoo_of_le hb] using h₂.symm)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf₀.trans hf₁) hf₂,
    ← intervalIntegral.integral_add_adjacent_intervals hf₀ hf₁,
    intervalIntegral.integral_congr_Ioo_of_le ha h₀,
    intervalIntegral.integral_congr_Ioo_of_le hab h₁,
    intervalIntegral.integral_congr_Ioo_of_le hb h₂]

private theorem integral_quadratic (A B a b : ℝ) :
    (∫ v in a..b, A * v ^ 2 + B * v) =
      (A * b ^ 3 / 3 + B * b ^ 2 / 2) - (A * a ^ 3 / 3 + B * a ^ 2 / 2) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro v _
    convert! ((((hasDerivAt_id v).pow 3).const_mul A).div_const 3).add
      ((((hasDerivAt_id v).pow 2).const_mul B).div_const 2) using 1
    simp only [id_eq]
    ring
  · exact (show Continuous (fun v : ℝ => A * v ^ 2 + B * v) by fun_prop).intervalIntegrable _ _

private theorem integral_xi_left (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (∫ v in (0 : ℝ)..a, v ^ 2 / (1 - v)) = -a ^ 2 / 2 - a - Real.log (1 - a) := by
  have hn (v : ℝ) (hv : v ∈ uIcc 0 a) : 1 - v ≠ 0 := by
    rw [uIcc_of_le ha] at hv
    linarith [hv.2]
  have hi : IntervalIntegrable (fun v : ℝ => v ^ 2 / (1 - v)) volume 0 a :=
    (ContinuousOn.div (by fun_prop) (by fun_prop) hn).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := a)
    (f := fun v : ℝ => -v ^ 2 / 2 - v - Real.log (1 - v))
    (f' := fun v => v ^ 2 / (1 - v)) (fun v hv => by
      convert! (((((hasDerivAt_id v).pow 2).neg.div_const 2).sub (hasDerivAt_id v)).sub
        (((hasDerivAt_id v).const_sub 1).log (hn v hv))) using 1
      simp only [id_eq]
      field_simp [hn v hv]
      ring) hi
  simpa using h

private theorem integral_xi_right (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    (∫ v in b..(1 : ℝ), 3 * v - 3 + 1 / v) =
      -3 / 2 - (3 * b ^ 2 / 2 - 3 * b + Real.log b) := by
  have hn (v : ℝ) (hv : v ∈ uIcc b 1) : v ≠ 0 := by
    rw [uIcc_of_le hb1] at hv
    linarith [hv.1]
  have hi : IntervalIntegrable (fun v : ℝ => 3 * v - 3 + 1 / v) volume b 1 :=
    (ContinuousOn.add (by fun_prop) (ContinuousOn.div (by fun_prop) (by fun_prop) hn)).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := b) (b := (1 : ℝ))
    (f := fun v : ℝ => 3 * v ^ 2 / 2 - 3 * v + Real.log v)
    (f' := fun v => 3 * v - 3 + 1 / v) (fun v hv => by
      convert! (((((hasDerivAt_id v).pow 2).const_mul 3).div_const 2).sub
        ((hasDerivAt_id v).const_mul 3)).add (Real.hasDerivAt_log (hn v hv)) using 1
      simp only [id_eq]
      ring) hi
  norm_num at h ⊢
  exact h

noncomputable def relaxedParameter (μ : ℝ) : ℝ := 2 / (2 + μ)

noncomputable def footruleClosed (r : ℝ) : ℝ := -2 * r ^ 2 + 6 * r - 5 + 1 / r

noncomputable def xiClosed (r : ℝ) : ℝ :=
  -4 * r ^ 2 + 20 * r - 17 + 2 / r - 1 / r ^ 2 - 12 * Real.log r

theorem relaxedParameter_mem (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    relaxedParameter μ ∈ Icc (1 / 2) 1 := by
  have hd : 0 < 2 + μ := by linarith [hμ.1]
  unfold relaxedParameter
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith [hμ.2]
  · apply (div_le_one hd).mpr
    linarith [hμ.1]

theorem relaxedParameter_inverse (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    μ = 2 / relaxedParameter μ - 2 := by
  have hd : 2 + μ ≠ 0 := by linarith [hμ.1]
  unfold relaxedParameter
  field_simp
  ring

private theorem profile_cutoffs (μ r v : ℝ) (hr : 0 < r) (hμ : μ = 2 / r - 2) :
    (v * (2 + μ) ≤ μ ↔ v ≤ 1 - r) ∧ (v * (2 + μ) ≤ 2 ↔ v ≤ r) := by
  have hmr : μ * r = 2 - 2 * r := by rw [hμ]; field_simp
  have hvr : v * (2 + μ) * r = 2 * v := by
    calc _ = v * (2 * r + μ * r) := by ring
         _ = _ := by rw [hmr]; ring
  constructor <;> constructor <;> intro h
  · have hh := mul_le_mul_of_nonneg_right h hr.le
    rw [hvr, hmr] at hh
    linarith
  · apply (mul_le_mul_iff_left₀ hr).mp
    rw [hvr, hmr]
    linarith
  · have hh := mul_le_mul_of_nonneg_right h hr.le
    rw [hvr] at hh
    linarith
  · apply (mul_le_mul_iff_left₀ hr).mp
    rw [hvr]
    linarith

private noncomputable def diagonalProfile (r v : ℝ) : ℝ :=
  if v ≤ 1 - r then 0 else if v ≤ r then v ^ 2 / r - (1 - r) / r * v else 2 * v - 1

private noncomputable def squareProfile (r v : ℝ) : ℝ :=
  if v ≤ 1 - r then v ^ 2 / (1 - v)
  else if v ≤ r then (1 - ((1 - r) / r) ^ 2) * v ^ 2 + ((1 - r) / r) ^ 2 * v
  else 3 * v - 3 + 1 / v

private theorem diagonalProfile_eq (μ r : ℝ) (hr : r ∈ Icc (1 / 2) 1)
    (hμ : μ = 2 / r - 2) (v : I) : (v : ℝ) * jensenLow μ v = diagonalProfile r v := by
  have hr0 : 0 < r := by linarith [hr.1]
  obtain ⟨hc₀, hc₁⟩ := profile_cutoffs μ r v hr0 hμ
  unfold jensenLow diagonalProfile
  simp only [hc₀, hc₁]
  split_ifs with h₀ h₁
  · ring
  · rw [hμ]
    field_simp
    ring
  · have hv : (v : ℝ) ≠ 0 := by linarith
    field_simp

private theorem squareProfile_eq (μ r : ℝ) (hr : r ∈ Icc (1 / 2) 1)
    (hμ : μ = 2 / r - 2) (v : I) :
    (v : ℝ) * jensenLow μ v ^ 2 + (1 - v) * jensenHigh μ v ^ 2 = squareProfile r v := by
  have hr0 : 0 < r := by linarith [hr.1]
  obtain ⟨hc₀, hc₁⟩ := profile_cutoffs μ r v hr0 hμ
  unfold jensenLow jensenHigh squareProfile
  simp only [hc₀, hc₁]
  split_ifs with h₀ h₁
  · have hv : 1 - (v : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  · rw [hμ]
    field_simp
    ring
  · have hv : (v : ℝ) ≠ 0 := by linarith
    field_simp
    ring

private theorem integral_diagonalProfile (r : ℝ) (hr : r ∈ Icc (1 / 2) 1) :
    6 * (∫ v in (0 : ℝ)..1, diagonalProfile r v) - 2 = footruleClosed r := by
  have hr0 : 0 < r := by linarith [hr.1]
  have ha : 0 ≤ 1 - r := by linarith [hr.2]
  have hab : 1 - r ≤ r := by linarith [hr.1]
  have he := integral_three_pieces (diagonalProfile r) (fun _ => 0)
    (fun v => (1 / r) * v ^ 2 + (-(1 - r) / r) * v) (fun v => 2 * v - 1)
    (1 - r) r ha hab hr.2
    (by intro v hv; simp only [diagonalProfile, ite_eq_left hv.2.le])
    (by intro v hv; simp only [diagonalProfile, ite_eq_right (not_le.mpr hv.1), ite_eq_left hv.2.le]; ring)
    (by intro v hv; simp only [diagonalProfile, ite_eq_right (not_le.mpr (lt_of_le_of_lt hab hv.1)),
      ite_eq_right (not_le.mpr hv.1)])
    (continuous_const.intervalIntegrable _ _)
    ((show Continuous (fun v : ℝ => (1 / r) * v ^ 2 + (-(1 - r) / r) * v) by fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun v : ℝ => 2 * v - 1) by fun_prop).intervalIntegrable _ _)
  have hR : (∫ v in r..(1 : ℝ), 2 * v - 1) = r - r ^ 2 := by
    rw [intervalIntegral.integral_sub ((show Continuous (fun v : ℝ => 2 * v) by fun_prop).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
    ring
  rw [he, intervalIntegral.integral_zero, integral_quadratic, hR]
  unfold footruleClosed
  field_simp
  ring

private theorem integral_squareProfile (r : ℝ) (hr : r ∈ Icc (1 / 2) 1) :
    6 * (∫ v in (0 : ℝ)..1, squareProfile r v) - 2 = xiClosed r := by
  have hr0 : 0 < r := by linarith [hr.1]
  have ha : 0 ≤ 1 - r := by linarith [hr.2]
  have ha1 : 1 - r < 1 := by linarith
  have hab : 1 - r ≤ r := by linarith [hr.1]
  have hiL : IntervalIntegrable (fun v : ℝ => v ^ 2 / (1 - v)) volume 0 (1 - r) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro v hv
    rw [uIcc_of_le ha] at hv
    linarith [hv.2]
  have hiR : IntervalIntegrable (fun v : ℝ => 3 * v - 3 + 1 / v) volume r 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add (by fun_prop)
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro v hv
    rw [uIcc_of_le hr.2] at hv
    linarith [hv.1]
  have he := integral_three_pieces (squareProfile r) (fun v => v ^ 2 / (1 - v))
    (fun v => (1 - ((1 - r) / r) ^ 2) * v ^ 2 + ((1 - r) / r) ^ 2 * v)
    (fun v => 3 * v - 3 + 1 / v) (1 - r) r ha hab hr.2
    (by intro v hv; simp only [squareProfile, ite_eq_left hv.2.le])
    (by intro v hv; simp only [squareProfile, ite_eq_right (not_le.mpr hv.1), ite_eq_left hv.2.le])
    (by intro v hv; simp only [squareProfile, ite_eq_right (not_le.mpr (lt_of_le_of_lt hab hv.1)),
      ite_eq_right (not_le.mpr hv.1)]) hiL
    ((show Continuous (fun v : ℝ => (1 - ((1 - r) / r) ^ 2) * v ^ 2 + ((1 - r) / r) ^ 2 * v)
      by fun_prop).intervalIntegrable _ _) hiR
  rw [he, integral_xi_left _ ha ha1, integral_quadratic, integral_xi_right _ hr0 hr.2]
  have hlog : 1 - (1 - r) = r := by ring
  rw [hlog]
  unfold xiClosed
  field_simp
  ring

/-- Proposition 3.1: exact footrule evaluation, including both parameter endpoints. -/
theorem relaxedFootrule_closed (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    relaxedFootrule μ = footruleClosed (relaxedParameter μ) := by
  unfold relaxedFootrule
  simp_rw [diagonalProfile_eq μ (relaxedParameter μ) (relaxedParameter_mem μ hμ)
    (relaxedParameter_inverse μ hμ)]
  rw [Copula.integral_unitInterval]
  exact integral_diagonalProfile _ (relaxedParameter_mem μ hμ)

/-- Proposition 3.1: exact xi evaluation, with the logarithmic term. -/
theorem relaxedXi_closed (μ : ℝ) (hμ : μ ∈ Icc 0 2) :
    relaxedXi μ = xiClosed (relaxedParameter μ) := by
  unfold relaxedXi
  simp_rw [squareProfile_eq μ (relaxedParameter μ) (relaxedParameter_mem μ hμ)
    (relaxedParameter_inverse μ hμ)]
  rw [Copula.integral_unitInterval]
  exact integral_squareProfile _ (relaxedParameter_mem μ hμ)

end Verification
