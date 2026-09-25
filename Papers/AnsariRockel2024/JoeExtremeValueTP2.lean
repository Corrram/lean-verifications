import Papers.AnsariRockel2024.JoeExtremeValue
import Verification.MTP2ConditionalIncreasing

/-! # A non-TP2 member of the asymmetric Joe extreme-value family

Table 5 marks Joe-EV density TP2 as `no*` (numerical, away from independence). For
`δ=1`, `α=β=1/2` and `u=t^a`, `v=t^b` the CDF is `t^(a+b-ab/(2(a+b)))`. With
`t=99/100`, the ordered rectangles `S=(0,t^180]`, `T=(t^180,t^30]`, `U=(t^45,t^20]`,
`V=(t^20,1]` violate the rectangle inequality implied by an MTP2 density. So this member
has no TP2 density. (The unit-weight member is Galambos, whose density-TP2 status the
paper leaves open, so the blanket claim is only checked at this member.)
-/

open ProbabilityTheory MeasureTheory Real Set Copula
open scoped unitInterval

namespace Papers.AnsariRockel2024

private noncomputable def tt : ℝ := 99 / 100

private noncomputable def half : I := ⟨1 / 2, by norm_num, by norm_num⟩

private noncomputable def pt (k : ℕ) : I :=
  ⟨tt ^ k, pow_nonneg (by norm_num [tt]) _, pow_le_one₀ (by norm_num [tt]) (by norm_num [tt])⟩

private theorem pt_coe (k : ℕ) : ((pt k : I) : ℝ) = tt ^ k := rfl

private theorem pt_mem {k : ℕ} (hk : 0 < k) : ((pt k : I) : ℝ) ∈ Ioo (0:ℝ) 1 :=
  ⟨pow_pos (by norm_num [tt]) _, pow_lt_one₀ (by norm_num [tt]) (by norm_num [tt]) hk.ne'⟩

private theorem log_pt (k : ℕ) : Real.log (tt ^ k) = k * Real.log tt := by
  rw [Real.log_pow]

/-- The `δ=1`, `α=β=1/2` Joe-EV CDF on powers of `t`. -/
private theorem cdf_pt (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (e : ℕ)
    (he : (e : ℝ) = a + b - a * b / (2 * (a + b))) :
    (Verification.joeExtremeValue 1 one_pos half half).cdf ![pt a, pt b] = tt ^ e := by
  rw [joeExtremeValue_cdf_interior 1 one_pos half half (pt a) (pt b)
    (by norm_num [half]) (by norm_num [half]) (pt_mem ha) (pt_mem hb)]
  simp only [pt_coe, half, log_pt]
  have hL : Real.log tt < 0 := Real.log_neg (by norm_num [tt]) (by norm_num [tt])
  have hA : (0:ℝ) < a := by exact_mod_cast ha
  have hB : (0:ℝ) < b := by exact_mod_cast hb
  have hx : 0 < (1/2 : ℝ) * -(a * Real.log tt) := by nlinarith
  have hy : 0 < (1/2 : ℝ) * -(b * Real.log tt) := by nlinarith
  rw [Real.rpow_neg_one, Real.rpow_neg_one, show (-1:ℝ)/1 = -1 by norm_num, Real.rpow_neg_one]
  have hexp : ((1/2 * -(a * Real.log tt))⁻¹ + (1/2 * -(b * Real.log tt))⁻¹)⁻¹ =
      ((a : ℝ) * b / (2 * (a + b))) * -Real.log tt := by
    rw [show (1/2 : ℝ) * -(a * Real.log tt) = a * (-Real.log tt) / 2 by ring,
      show (1/2 : ℝ) * -(b * Real.log tt) = b * (-Real.log tt) / 2 by ring]
    have hl : 0 < -Real.log tt := by linarith
    generalize -Real.log tt = l at hl ⊢
    field_simp
    ring
  rw [hexp]
  have htp : 0 < tt := by norm_num [tt]
  have hE : Real.exp (((a : ℝ) * b / (2 * (a + b))) * -Real.log tt) =
      tt ^ (-((a : ℝ) * b / (2 * (a + b)))) := by
    rw [Real.rpow_def_of_pos htp]; congr 1; ring
  rw [hE, ← Real.rpow_natCast tt e, he, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_add htp, ← Real.rpow_add htp]
  congr 1

theorem joeExtremeValue_witness_not_mtp2 :
    ¬ (Verification.joeExtremeValue 1 one_pos half half).HasMTP2Density := by
  intro h
  set C := Verification.joeExtremeValue 1 one_pos half half
  have hle : ∀ {i j : ℕ}, j ≤ i → pt i ≤ pt j := by
    intro i j hij
    show tt ^ i ≤ tt ^ j
    exact pow_le_pow_of_le_one (by norm_num [tt]) (by norm_num [tt]) hij
  have he := Verification.mtp2_ordered_rectangles h (Ioc 0 (pt 180)) (Ioc (pt 180) (pt 30))
    (Ioc (pt 45) (pt 20)) (Ioc (pt 20) 1)
    measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc measurableSet_Ioc
    (fun x hx y hy => hx.2.trans hy.1.le) (fun x hx y hy => hx.2.trans hy.1.le)
  rw [Verification.measureReal_coordinate_rectangle C 0 (pt 180) (pt 20) 1 (pt 180).2.1
      (pt 20).2.2,
    Verification.measureReal_coordinate_rectangle C (pt 180) (pt 30) (pt 45) (pt 20)
      (hle (by norm_num)) (hle (by norm_num)),
    Verification.measureReal_coordinate_rectangle C 0 (pt 180) (pt 45) (pt 20) (pt 180).2.1
      (hle (by norm_num)),
    Verification.measureReal_coordinate_rectangle C (pt 180) (pt 30) (pt 20) 1
      (hle (by norm_num)) (pt 20).2.2] at he
  simp only [Copula.cdf_two_zero_left, Copula.cdf_two_one_right, sub_zero, add_zero] at he
  rw [cdf_pt 180 20 (by norm_num) (by norm_num) 191 (by norm_num),
    cdf_pt 30 20 (by norm_num) (by norm_num) 44 (by norm_num),
    cdf_pt 180 45 (by norm_num) (by norm_num) 207 (by norm_num),
    cdf_pt 30 45 (by norm_num) (by norm_num) 66 (by norm_num)] at he
  simp only [pt_coe] at he
  norm_num [tt] at he

end Papers.AnsariRockel2024
