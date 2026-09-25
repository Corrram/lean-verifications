import Copula.Families.Gumbel
import Verification.MTP2ConditionalIncreasing

/-! # A non-TP2 Tawn member away from the Gumbel subfamily

Table 5 marks Tawn density TP2 as `no*` (numerical). At `θ=2`, `α=β=1/2` and
`u=t^m`, `v=t^n` the CDF is `t^((m+n+s)/2)` when `m²+n²=s²`. The Pythagorean
double pairs `(91,60,109)`, `(91,312,325)`, `(25,60,65)`, `(25,312,313)` give the ordered
rectangles `S=(t^91,t^25]`, `T=(t^25,1]`, `U=(0,t^312]`, `V=(t^312,t^60]`, which at
`t=99/100` violate the rectangle inequality forced by an MTP2 density. Together with the
Gumbel (unit-weight) members, which do have TP2 densities, this shows the Tawn cell is
parameter dependent: the exclusion holds for this member.
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

private noncomputable def tq : ℝ := 99 / 100

private noncomputable def halfI : I := ⟨1 / 2, by norm_num, by norm_num⟩

private noncomputable def tpt (k : ℕ) : I :=
  ⟨tq ^ k, pow_nonneg (by norm_num [tq]) _, pow_le_one₀ (by norm_num [tq]) (by norm_num [tq])⟩

private theorem tpt_coe (k : ℕ) : ((tpt k : I) : ℝ) = tq ^ k := rfl

private theorem tpt_ne_zero (k : ℕ) : tpt k ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp only [tpt_coe, Set.Icc.coe_zero] at this
  exact (pow_pos (by norm_num [tq] : (0:ℝ) < tq) k).ne' this

/-- The `θ=2`, `α=β=1/2` Tawn CDF on Pythagorean powers of `t`. -/
private theorem tawn_cdf_pt (m n s e : ℕ) (hs : m ^ 2 + n ^ 2 = s ^ 2) (he : m + n + s = 2 * e) :
    (tawn 2 (by norm_num) halfI halfI).cdf ![tpt m, tpt n] = tq ^ e := by
  rw [tawn_cdf_positive 2 (by norm_num) halfI halfI (tpt m) (tpt n) (tpt_ne_zero m)
    (tpt_ne_zero n)]
  simp only [tpt_coe, halfI]
  have ht : 0 < tq := by norm_num [tq]
  set L := -Real.log tq
  have hL : 0 < L := neg_pos.mpr (Real.log_neg ht (by norm_num [tq]))
  have hlogm : -Real.log (tq ^ m) = m * L := by rw [Real.log_pow]; ring
  have hlogn : -Real.log (tq ^ n) = n * L := by rw [Real.log_pow]; ring
  rw [hlogm, hlogn]
  have hsq : ((1/2 : ℝ) * (m * L)) ^ (2:ℝ) + ((1/2) * (n * L)) ^ (2:ℝ) = ((s : ℝ) * L / 2) ^ 2 := by
    rw [Real.rpow_two, Real.rpow_two]
    have : ((m:ℝ)) ^ 2 + (n:ℝ) ^ 2 = (s:ℝ) ^ 2 := by exact_mod_cast hs
    linear_combination (L ^ 2 / 4) * this
  rw [hsq, show ((2:ℝ))⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (by positivity)]
  -- everything is a power of `tq`
  have hpow (r : ℝ) : Real.exp (-(r * L)) = tq ^ r := by
    rw [Real.rpow_def_of_pos ht]; congr 1; simp only [L]; ring
  have h1 : (tq ^ m : ℝ) ^ (1 - (1/2 : ℝ)) = tq ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; ring
  have h2 : (tq ^ n : ℝ) ^ (1 - (1/2 : ℝ)) = tq ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; ring
  rw [h1, h2, show -((s : ℝ) * L / 2) = -(((s:ℝ) / 2) * L) by ring, hpow,
    ← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_natCast]
  congr 1
  have : (m : ℝ) + n + s = 2 * e := by exact_mod_cast he
  linarith

theorem tawn_witness_not_mtp2 :
    ¬ (tawn 2 (by norm_num) halfI halfI).HasMTP2Density := by
  intro h
  set C := tawn 2 (by norm_num) halfI halfI
  have hle : ∀ {i j : ℕ}, j ≤ i → tpt i ≤ tpt j := by
    intro i j hij
    show tq ^ i ≤ tq ^ j
    exact pow_le_pow_of_le_one (by norm_num [tq]) (by norm_num [tq]) hij
  have he := Verification.mtp2_ordered_rectangles h (Ioc (tpt 91) (tpt 25)) (Ioc (tpt 25) 1)
    (Ioc 0 (tpt 312)) (Ioc (tpt 312) (tpt 60))
    measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc
    (fun x hx y hy => hx.2.trans hy.1.le) (fun x hx y hy => hx.2.trans hy.1.le)
  rw [Verification.measureReal_coordinate_rectangle C (tpt 91) (tpt 25) (tpt 312) (tpt 60)
      (hle (by norm_num)) (hle (by norm_num)),
    Verification.measureReal_coordinate_rectangle C (tpt 25) 1 0 (tpt 312)
      (tpt 25).2.2 (tpt 312).2.1,
    Verification.measureReal_coordinate_rectangle C (tpt 91) (tpt 25) 0 (tpt 312)
      (hle (by norm_num)) (tpt 312).2.1,
    Verification.measureReal_coordinate_rectangle C (tpt 25) 1 (tpt 312) (tpt 60)
      (tpt 25).2.2 (hle (by norm_num))] at he
  simp only [Copula.cdf_two_zero_right, Copula.cdf_two_one_left, sub_zero, add_zero] at he
  rw [tawn_cdf_pt 25 60 65 75 (by norm_num) (by norm_num),
    tawn_cdf_pt 91 60 109 130 (by norm_num) (by norm_num),
    tawn_cdf_pt 25 312 313 325 (by norm_num) (by norm_num),
    tawn_cdf_pt 91 312 325 364 (by norm_num) (by norm_num)] at he
  simp only [tpt_coe] at he
  unfold tq at he
  -- split the large powers so that each evaluated exponent stays small
  rw [show (99/100:ℝ)^312=(99/100)^200*(99/100)^112 by rw [← pow_add],
    show (99/100:ℝ)^325=(99/100)^200*(99/100)^125 by rw [← pow_add],
    show (99/100:ℝ)^364=(99/100)^200*(99/100)^164 by rw [← pow_add]] at he
  norm_num at he

end Papers.AnsariRockel2024
