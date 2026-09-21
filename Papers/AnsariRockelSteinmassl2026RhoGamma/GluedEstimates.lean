import Papers.AnsariRockelSteinmassl2026RhoGamma.ArcEstimates

/-! # A uniform cubic remainder for the glued boundary coordinates -/

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

/-- Quantitative form of Remark 2.2, before substituting a concrete boundary arc. -/
theorem glued_cubic_estimate {s a z m q : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1 / 4) (ha : 0 ≤ a) (has : a ≤ s) (hz : z = 1 - a)
    (hm0 : 0 ≤ m) (hms : m ≤ s) (hq0 : 0 ≤ q)
    (hm : |m - s / 2| ≤ s ^ 2 / 2) (hq : |q - s ^ 2 / 4| ≤ 2 * s ^ 3) :
    let H := 2 * a ^ 2 + z ^ 2 * m
    let J := 2 * a ^ 3 + 3 / 2 * z ^ 3 * q
    s / 16 ≤ H ∧ |J - 3 / 2 * H ^ 2| ≤ 98304 * H ^ 3 := by
  let H := 2 * a ^ 2 + z ^ 2 * m
  let J := 2 * a ^ 3 + 3 / 2 * z ^ 3 * q
  change s / 16 ≤ H ∧ |J - 3 / 2 * H ^ 2| ≤ 98304 * H ^ 3
  have hz0 : 0 ≤ z := by linarith
  have hz1 : z ≤ 1 := by linarith
  have hzhalf : 1 / 2 ≤ z := by linarith
  have hzs : z ^ 2 ≤ 1 := by nlinarith
  have ha2 : a ^ 2 ≤ s ^ 2 := by nlinarith
  have ha3 : a ^ 3 ≤ s ^ 3 := by gcongr
  have hmlo := (abs_le.mp hm).1
  have hmhi := (abs_le.mp hm).2
  have hqlo := (abs_le.mp hq).1
  have hqhi := (abs_le.mp hq).2
  have hms4 : s / 4 ≤ m := by nlinarith
  have hHlo : s / 16 ≤ H := by
    have hh := mul_le_mul (show (1 : ℝ) / 4 ≤ z ^ 2 by nlinarith) hms4
      (by positivity : 0 ≤ s / 4) (sq_nonneg z)
    dsimp [H]
    nlinarith only [hh, sq_nonneg a]
  have hHhi : H ≤ 3 / 2 * s := by
    have hh := mul_le_mul_of_nonneg_right hzs hm0
    dsimp [H]
    nlinarith
  have hzm : (1 - z ^ 2) * m ≤ 2 * s ^ 2 := by
    have hb : 1 - z ^ 2 ≤ 2 * a := by nlinarith [sq_nonneg a]
    have hh := mul_le_mul hb hms hm0 (by positivity : 0 ≤ 2 * a)
    have hh' := mul_le_mul_of_nonneg_right has hs
    nlinarith only [hh, hh']
  have hHerr : |H - s / 2| ≤ 5 * s ^ 2 := by
    apply abs_le.mpr
    dsimp [H]
    constructor
    · nlinarith only [hzm, hmlo, sq_nonneg a, sq_nonneg s]
    · have hh := mul_le_mul_of_nonneg_right hzs hm0
      nlinarith only [hh, hmhi, ha2, sq_nonneg s]
  have hqbound : q ≤ 3 / 4 * s ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hs1 (sq_nonneg s)
    nlinarith only [hqhi, hh]
  have hz3 : z ^ 3 ≤ 1 := by nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hzs)]
  have hz3err : 1 - z ^ 3 ≤ 3 * a := by
    have hh := mul_nonneg (sq_nonneg a) (show 0 ≤ 3 - a by linarith)
    rw [hz]
    nlinarith only [hh]
  have hzq : (1 - z ^ 3) * q ≤ 9 / 4 * s ^ 3 := by
    have hh := mul_le_mul hz3err hqbound hq0 (by positivity : 0 ≤ 3 * a)
    have hh' := mul_le_mul_of_nonneg_right has (sq_nonneg s)
    nlinarith only [hh, hh']
  have hJerr : |J - 3 / 8 * s ^ 2| ≤ 9 * s ^ 3 := by
    apply abs_le.mpr
    dsimp [J]
    constructor
    · nlinarith only [hzq, hqlo, pow_nonneg ha 3, pow_nonneg hs 3]
    · have hh := mul_le_mul_of_nonneg_right hz3 hq0
      nlinarith only [hh, hqhi, ha3, pow_nonneg hs 3]
  have hH0 : 0 ≤ H := by linarith
  have hHsq : |H ^ 2 - s ^ 2 / 4| ≤ 10 * s ^ 3 := by
    rw [show H ^ 2 - s ^ 2 / 4 = (H - s / 2) * (H + s / 2) by ring,
      abs_mul, abs_of_nonneg (by linarith : 0 ≤ H + s / 2)]
    have hh := mul_le_mul hHerr (show H + s / 2 ≤ 2 * s by linarith)
      (by linarith : 0 ≤ H + s / 2) (by positivity : 0 ≤ 5 * s ^ 2)
    nlinarith only [hh]
  have herr : |J - 3 / 2 * H ^ 2| ≤ 24 * s ^ 3 := by
    have h1 := (abs_le.mp hJerr)
    have h2 := (abs_le.mp hHsq)
    apply abs_le.mpr
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hc : s ^ 3 ≤ (16 * H) ^ 3 := by gcongr; linarith
  exact ⟨hHlo, herr.trans (by nlinarith only [hc])⟩

end Papers.AnsariRockelSteinmassl2026RhoGamma
