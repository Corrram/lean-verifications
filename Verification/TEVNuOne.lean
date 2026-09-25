import Verification.TEVPickandsFormula
import Verification.TEVStudentDensity
import Verification.MTP2ConditionalIncreasing
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # The t-EV copula at `ν=1`, `r=0`

With two degrees of freedom the Student-t CDF is `T₂(z)=1/2+z/(2√(2+z²))`. At `ν=1`,
`r=0` the t-EV stable tail function becomes `(x+y+√(x²+y²))/2`, i.e. the Tawn copula with
`θ=2`, `α=β=1/2`. On Pythagorean powers `u=t^m`, `v=t^n` (`m²+n²=s²`) the CDF is
`t^((m+n+s)/2)`, and the same rectangle witness as for Tawn excludes a TP2 density.
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Verification

noncomputable def studentT2Closed (z : ℝ) : ℝ := 1 / 2 + z / (2 * Real.sqrt (2 + z ^ 2))

theorem studentMarginalPDF_two (z : ℝ) :
    studentMarginalPDF 2 z = 1 / Real.sqrt (2 + z ^ 2) ^ 3 := by
  unfold studentMarginalPDF
  have hG : Real.Gamma (2 / 2 + 1 / 2) = Real.sqrt Real.pi / 2 := by
    rw [show (2:ℝ) / 2 + 1 / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have h1 : (2:ℝ) / 2 = 1 := by norm_num
  rw [hG, h1, Real.rpow_one, Real.Gamma_one]
  have hb : (0:ℝ) < 1 + z ^ 2 / 2 := by positivity
  have hpow : (1 + z ^ 2 / 2) ^ ((1:ℝ) + 1 / 2) = Real.sqrt ((2 + z ^ 2) / 2) ^ 3 := by
    rw [show (1:ℝ) + z ^ 2 / 2 = (2 + z ^ 2) / 2 by ring, Real.sqrt_eq_rpow,
      ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  rw [hpow, Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) Real.pi]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsp : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsz : 0 < Real.sqrt (2 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  exact h22

theorem hasDerivAt_studentT2Closed (z : ℝ) :
    HasDerivAt studentT2Closed (1 / Real.sqrt (2 + z ^ 2) ^ 3) z := by
  have hp : (0:ℝ) < 2 + z ^ 2 := by positivity
  have hs : HasDerivAt (fun z : ℝ => Real.sqrt (2 + z ^ 2))
      ((2 * z) / (2 * Real.sqrt (2 + z ^ 2))) z := by
    have := ((hasDerivAt_pow 2 z).const_add 2).sqrt hp.ne'
    convert this using 1; ring
  have hq := (hasDerivAt_id z).div (hs.const_mul 2)
    (mul_pos (by norm_num : (0:ℝ) < 2) (Real.sqrt_pos.mpr hp)).ne'
  unfold studentT2Closed
  convert hq.const_add (1 / 2) using 1
  · funext x; simp
  · have hsz : 0 < Real.sqrt (2 + z ^ 2) := Real.sqrt_pos.mpr hp
    have hsq : Real.sqrt (2 + z ^ 2) ^ 2 = 2 + z ^ 2 := Real.sq_sqrt hp.le
    simp only [id]
    field_simp
    rw [hsq]
    ring

/-- The two-degree-of-freedom Student-t CDF in closed form. -/
theorem studentTCDF_two (z : ℝ) : studentTCDF 2 z = studentT2Closed z := by
  have hd : ∀ x, HasDerivAt (fun x => studentTCDF 2 x - studentT2Closed x) 0 x := by
    intro x
    have := (studentTCDF_hasDerivAt 2 (by norm_num) x).sub (hasDerivAt_studentT2Closed x)
    rwa [studentMarginalPDF_two, sub_self] at this
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt)
    (fun x => (hd x).deriv) z 0
  have h0 : studentTCDF 2 0 = studentT2Closed 0 := by
    rw [studentTCDF_zero 2 (by norm_num)]; simp [studentT2Closed]
  linarith

/-- The `ν=1`, `r=0` t-EV CDF on Pythagorean powers of `t∈(0,1)`. -/
theorem tEV_one_zero_cdf_pow {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (m n s e : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (hs : m ^ 2 + n ^ 2 = s ^ 2) (he : m + n + s = 2 * e) (u v : I)
    (hu : (u : ℝ) = t ^ m) (hv : (v : ℝ) = t ^ n) :
    (tEV 1 0 one_pos ⟨by norm_num, by norm_num⟩).cdf ![u, v] = t ^ e := by
  have hu' : (u : ℝ) ∈ Ioo (0:ℝ) 1 := by
    rw [hu]; exact ⟨pow_pos ht0 _, pow_lt_one₀ ht0.le ht1 hm.ne'⟩
  have hv' : (v : ℝ) ∈ Ioo (0:ℝ) 1 := by
    rw [hv]; exact ⟨pow_pos ht0 _, pow_lt_one₀ ht0.le ht1 hn.ne'⟩
  have h := tEV_cdf_interior 1 0 one_pos ⟨by norm_num, by norm_num⟩ u v hu' hv'
  rw [h]
  set L := -Real.log t
  have hL : 0 < L := neg_pos.mpr (Real.log_neg ht0 ht1)
  have hx : -Real.log (u : ℝ) = m * L := by rw [hu, Real.log_pow]; ring
  have hy : -Real.log (v : ℝ) = n * L := by rw [hv, Real.log_pow]; ring
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hsR : ((m:ℝ)) ^ 2 + (n:ℝ) ^ 2 = (s:ℝ) ^ 2 := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by
    have : 0 < s := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · rw [h0] at hs
        simp at hs
        omega
      · exact h0
    exact_mod_cast this
  have harg (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      tEVArg 1 0 ((a / b) ^ ((1:ℝ) / 1)) = Real.sqrt 2 * (a / b) := by
    unfold tEVArg; norm_num
  rw [show (1:ℝ) + 1 = 2 by norm_num, hx, hy, harg _ _ (by positivity) (by positivity), harg _ _ (by positivity) (by positivity),
    studentTCDF_two, studentTCDF_two]
  unfold studentT2Closed
  -- evaluate the square roots
  have hq (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a ^ 2 + b ^ 2 = c ^ 2) :
      Real.sqrt 2 * (a * L / (b * L)) / (2 * Real.sqrt (2 + (Real.sqrt 2 * (a * L / (b * L))) ^ 2))
        = a / (2 * c) := by
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hrad : 2 + (Real.sqrt 2 * (a * L / (b * L))) ^ 2 = (Real.sqrt 2 * (c / b)) ^ 2 := by
      rw [mul_pow, mul_pow, h2, div_pow, div_pow, ← habc]
      field_simp
      ring
    rw [hrad, Real.sqrt_sq (by positivity)]
    field_simp
  have hsR' : ((n:ℝ)) ^ 2 + (m:ℝ) ^ 2 = (s:ℝ) ^ 2 := by linarith
  rw [hq _ _ _ hmR hnR hs0 hsR, hq _ _ _ hnR hmR hs0 hsR']
  have hexp : -(m * L * (1 / 2 + m / (2 * s)) + n * L * (1 / 2 + n / (2 * s))) =
      (e : ℝ) * Real.log t := by
    have heR : (m:ℝ) + n + s = 2 * e := by exact_mod_cast he
    simp only [L]
    field_simp
    linear_combination (Real.log t * s) * heR + Real.log t * hsR
  rw [hexp, ← Real.log_pow, Real.exp_log (pow_pos ht0 _)]

end Verification
