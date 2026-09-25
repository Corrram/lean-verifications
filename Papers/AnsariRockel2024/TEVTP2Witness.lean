import Verification.TEVNuOne
import Verification.MTP2ConditionalIncreasing

/-! # A non-TP2 t-EV member

Table 5 marks t-EV density TP2 as `no*` (numerical). At `ν=1`, `r=0` the t-EV copula has
CDF `t^((m+n+s)/2)` on Pythagorean powers `u=t^m`, `v=t^n` (it coincides with the
`θ=2`, `α=β=1/2` Tawn copula), and the Tawn rectangle witness applies verbatim.
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

private noncomputable def tq2 : ℝ := 99 / 100


private noncomputable def tpt2 (k : ℕ) : I :=
  ⟨tq2 ^ k, pow_nonneg (by norm_num [tq2]) _, pow_le_one₀ (by norm_num [tq2]) (by norm_num [tq2])⟩

private theorem tpt2_coe (k : ℕ) : ((tpt2 k : I) : ℝ) = tq2 ^ k := rfl

private theorem tpt2_ne_zero (k : ℕ) : tpt2 k ≠ 0 := by
  intro h
  have := congrArg Subtype.val h
  simp only [tpt2_coe, Set.Icc.coe_zero] at this
  exact (pow_pos (by norm_num [tq2] : (0:ℝ) < tq2) k).ne' this

private theorem tEV_cdf_pt (m n s e : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hs : m ^ 2 + n ^ 2 = s ^ 2) (he : m + n + s = 2 * e) :
    (Verification.tEV 1 0 one_pos ⟨by norm_num, by norm_num⟩).cdf ![tpt2 m, tpt2 n] = tq2 ^ e :=
  Verification.tEV_one_zero_cdf_pow (by norm_num [tq2]) (by norm_num [tq2]) m n s e hm hn hs he
    _ _ rfl rfl

theorem tEV_witness_not_mtp2 :
    ¬ (Verification.tEV 1 0 one_pos ⟨by norm_num, by norm_num⟩).HasMTP2Density := by
  intro h
  set C := Verification.tEV 1 0 one_pos ⟨by norm_num, by norm_num⟩
  have hle : ∀ {i j : ℕ}, j ≤ i → tpt2 i ≤ tpt2 j := by
    intro i j hij
    show tq2 ^ i ≤ tq2 ^ j
    exact pow_le_pow_of_le_one (by norm_num [tq2]) (by norm_num [tq2]) hij
  have he := Verification.mtp2_ordered_rectangles h (Ioc (tpt2 91) (tpt2 25)) (Ioc (tpt2 25) 1)
    (Ioc 0 (tpt2 312)) (Ioc (tpt2 312) (tpt2 60))
    measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc
    (fun x hx y hy => hx.2.trans hy.1.le) (fun x hx y hy => hx.2.trans hy.1.le)
  rw [Verification.measureReal_coordinate_rectangle C (tpt2 91) (tpt2 25) (tpt2 312) (tpt2 60)
      (hle (by norm_num)) (hle (by norm_num)),
    Verification.measureReal_coordinate_rectangle C (tpt2 25) 1 0 (tpt2 312)
      (tpt2 25).2.2 (tpt2 312).2.1,
    Verification.measureReal_coordinate_rectangle C (tpt2 91) (tpt2 25) 0 (tpt2 312)
      (hle (by norm_num)) (tpt2 312).2.1,
    Verification.measureReal_coordinate_rectangle C (tpt2 25) 1 (tpt2 312) (tpt2 60)
      (tpt2 25).2.2 (hle (by norm_num))] at he
  simp only [Copula.cdf_two_zero_right, Copula.cdf_two_one_left, sub_zero, add_zero] at he
  rw [tEV_cdf_pt 25 60 65 75 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    tEV_cdf_pt 91 60 109 130 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    tEV_cdf_pt 25 312 313 325 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    tEV_cdf_pt 91 312 325 364 (by norm_num) (by norm_num) (by norm_num) (by norm_num)] at he
  simp only [tpt2_coe] at he
  unfold tq2 at he
  -- split the large powers so that each evaluated exponent stays small
  rw [show (99/100:ℝ)^312=(99/100)^200*(99/100)^112 by rw [← pow_add],
    show (99/100:ℝ)^325=(99/100)^200*(99/100)^125 by rw [← pow_add],
    show (99/100:ℝ)^364=(99/100)^200*(99/100)^164 by rw [← pow_add]] at he
  norm_num at he

end Papers.AnsariRockel2024
