import Papers.AnsariRockelSteinmassl2026RhoGamma.SourceBranches

/-! # Uniform estimates on all finite boundary arcs -/

open ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

/-- The spline width is quadratically small, uniformly in its integer index. -/
theorem arc_width_bound {n v s : ℝ} (hn : 1 ≤ n) (_hv : 0 ≤ v) (hs : 0 ≤ s)
    (hnv : n * (n + 1) * v ≤ 1 / 2) (hns : 1 ≤ (n + 1) * s) : v ≤ s ^ 2 := by
  have hns' : 1 / 2 ≤ n * s := by nlinarith [mul_nonneg (sub_nonneg.mpr hn) hs]
  have hp := mul_le_mul hns' hns (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ n * s)
  have hk : 0 < n * (n + 1) := by positivity
  have hh : n * (n + 1) * v ≤ n * (n + 1) * s ^ 2 := by nlinarith only [hp, hnv]
  exact (mul_le_mul_iff_right₀ hk).mp hh

/-- First and second distance moments have uniform quadratic/cubic errors. -/
theorem source_moment_estimates {k ell delta s : ℝ}
    (hk : 0 ≤ k) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (he : s = 2 * ell + delta) (hv : |delta| ≤ s ^ 2) (hkv : k * |delta| ≤ 1 / 2) :
    let m := ell + k * delta * |delta|
    let q := ell * (2 * m - ell) + 2 / 3 * k * |delta| ^ 3
    0 ≤ m ∧ m ≤ s ∧ |m - s / 2| ≤ s ^ 2 / 2 ∧ |q - s ^ 2 / 4| ≤ 2 * s ^ 3 := by
  let v := |delta|
  let m := ell + k * delta * v
  let q := ell * (2 * m - ell) + 2 / 3 * k * v ^ 3
  change 0 ≤ m ∧ m ≤ s ∧ |m - s / 2| ≤ s ^ 2 / 2 ∧ |q - s ^ 2 / 4| ≤ 2 * s ^ 3
  have hv0 : 0 ≤ v := abs_nonneg _
  have hkv0 : 0 ≤ k * v := mul_nonneg hk hv0
  have hvs : v ≤ s := hv.trans (by nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)])
  have hm : m - s / 2 = delta * (k * v - 1 / 2) := by dsimp [m]; nlinarith only [he]
  have hmabs : |m - s / 2| ≤ v / 2 := by
    rw [hm, abs_mul, abs_of_nonpos (by linarith : k * v - 1 / 2 ≤ 0)]
    change v * -(k * v - 1 / 2) ≤ v / 2
    nlinarith only [mul_nonneg hv0 hkv0]
  have hmlo : 0 ≤ m := by have hh := (abs_le.mp hmabs).1; linarith
  have hmhi : m ≤ s := by have hh := (abs_le.mp hmabs).2; linarith
  have hmabs' : |m - s / 2| ≤ s ^ 2 / 2 := hmabs.trans (by linarith)
  have hd2 : delta ^ 2 = v ^ 2 := (sq_abs delta).symm
  have hvariance : q - m ^ 2 = v ^ 2 * (2 / 3 * (k * v) - (k * v) ^ 2) := by
    dsimp [q, m]
    nlinarith only [congrArg (fun r : ℝ => k ^ 2 * v ^ 2 * r) hd2]
  have hb0 : 0 ≤ 2 / 3 * (k * v) - (k * v) ^ 2 := by
    have hh := mul_nonneg hkv0 (show 0 ≤ 2 / 3 - k * v by linarith)
    nlinarith only [hh]
  have hb1 : 2 / 3 * (k * v) - (k * v) ^ 2 ≤ 1 / 3 := by nlinarith only [hkv, sq_nonneg (k * v)]
  have hvar0 : 0 ≤ q - m ^ 2 := by rw [hvariance]; positivity
  have hvar1 : q - m ^ 2 ≤ v ^ 2 / 3 := by
    rw [hvariance]
    nlinarith only [mul_le_mul_of_nonneg_left hb1 (sq_nonneg v)]
  have hvsq : v ^ 2 ≤ s ^ 4 := by nlinarith only [hv, hv0, sq_nonneg (v - s ^ 2)]
  have hs43 : s ^ 4 ≤ s ^ 3 := by nlinarith only [mul_nonneg (pow_nonneg hs 3) (sub_nonneg.mpr hs1)]
  have hmsq : |m ^ 2 - s ^ 2 / 4| ≤ 3 / 4 * s ^ 3 := by
    rw [show m ^ 2 - s ^ 2 / 4 = (m - s / 2) * (m + s / 2) by ring, abs_mul,
      abs_of_nonneg (by linarith : 0 ≤ m + s / 2)]
    have hh := mul_le_mul hmabs' (show m + s / 2 ≤ 3 / 2 * s by linarith)
      (by linarith : 0 ≤ m + s / 2) (by positivity : 0 ≤ s ^ 2 / 2)
    nlinarith only [hh]
  refine ⟨hmlo, hmhi, hmabs', ?_⟩
  calc
    |q - s ^ 2 / 4| = |(q - m ^ 2) + (m ^ 2 - s ^ 2 / 4)| := by congr 1; ring
    _ ≤ |q - m ^ 2| + |m ^ 2 - s ^ 2 / 4| := abs_add_le _ _
    _ ≤ 2 * s ^ 3 := by rw [abs_of_nonneg hvar0]; nlinarith only [hvar1, hvsq, hs43, hmsq, pow_nonneg hs 3]

end Papers.AnsariRockelSteinmassl2026RhoGamma
