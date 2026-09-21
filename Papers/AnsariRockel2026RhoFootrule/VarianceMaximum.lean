import Papers.AnsariRockel2026RhoFootrule.MeanVariance

/-! # Remark 1.8(c): the exact universal maximum variance of absolute displacement -/

open MeasureTheory ProbabilityTheory

namespace Papers.AnsariRockel2026RhoFootrule

private noncomputable def goldenRoot : ℝ := (Real.sqrt 5 - 1) / 2

private theorem golden_properties :
    0 ≤ goldenRoot ∧ goldenRoot ≤ 1 ∧ goldenRoot ^ 2 + goldenRoot = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  dsimp [goldenRoot]
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

private theorem variance_factor {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    5 * (3 - Real.sqrt 5) / 24 - maximumVariance m =
      (Real.sqrt (1 - 2 * m) - goldenRoot) ^ 2 *
        ((Real.sqrt (1 - 2 * m)) ^ 2 / 4 +
          (goldenRoot / 2 + 1 / 3) * Real.sqrt (1 - 2 * m) + (3 - goldenRoot) / 12) := by
  have hr := Real.sq_sqrt (show 0 ≤ 1 - 2 * m by linarith [hm.2])
  have hm' : m = (1 - (Real.sqrt (1 - 2 * m)) ^ 2) / 2 := by linarith
  have ha2 : goldenRoot ^ 2 = 1 - goldenRoot := by linarith [golden_properties.2.2]
  have ha3 : goldenRoot ^ 3 = 2 * goldenRoot - 1 := by
    rw [pow_succ, ha2]
    nlinarith only [ha2]
  have hconst : 5 * (3 - Real.sqrt 5) / 24 = (5 - 5 * goldenRoot) / 12 := by unfold goldenRoot; ring
  unfold maximumVariance
  rw [hconst]
  conv_lhs => rw [hm']
  rw [show 1 - 2 * ((1 - (Real.sqrt (1 - 2 * m)) ^ 2) / 2) = (Real.sqrt (1 - 2 * m)) ^ 2 by ring,
    Real.sqrt_sq (Real.sqrt_nonneg _)]
  ring_nf
  rw [ha3, ha2]
  ring

/-- The exact global upper bound on the source maximum-variance function. -/
theorem maximumVariance_global_bound {m : ℝ} (hm : m ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    maximumVariance m ≤ 5 * (3 - Real.sqrt 5) / 24 := by
  have hf := variance_factor hm
  have hc : 0 ≤ (Real.sqrt (1 - 2 * m)) ^ 2 / 4 +
      (goldenRoot / 2 + 1 / 3) * Real.sqrt (1 - 2 * m) + (3 - goldenRoot) / 12 := by
    have h1 := golden_properties.1
    have h2 := golden_properties.2.1
    have h3 : 0 ≤ (3 - goldenRoot) / 12 := by linarith
    positivity
  have hh := mul_nonneg (sq_nonneg (Real.sqrt (1 - 2 * m) - goldenRoot)) hc
  linarith only [hf, hh]

/-- Equation (25): the exact universal interval for variance. -/
theorem universal_variance_bounds (C : Copula 2) :
    0 ≤ distanceVariance C ∧ distanceVariance C ≤ 5 * (3 - Real.sqrt 5) / 24 :=
  ⟨integral_nonneg (fun _ => sq_nonneg _),
    (sharp_variance_bounds C).2.trans (maximumVariance_global_bound (meanDistance_mem C))⟩

/-- The mean corresponding to the source maximizing footrule x0. -/
noncomputable def maximumVarianceMean : ℝ := (Real.sqrt 5 - 1) / 4

private theorem maximumVarianceMean_mem : maximumVarianceMean ∈ Set.Icc (0 : ℝ) (1 / 2) := by
  have h1 := golden_properties.1
  have h2 := golden_properties.2.1
  have he : maximumVarianceMean = goldenRoot / 2 := by unfold maximumVarianceMean goldenRoot; ring
  rw [he]
  constructor <;> linarith

/-- Exact evaluation at the golden-ratio contact parameter. -/
theorem maximumVariance_at_maximizer :
    maximumVariance maximumVarianceMean = 5 * (3 - Real.sqrt 5) / 24 := by
  have he : 1 - 2 * maximumVarianceMean = goldenRoot ^ 2 := by
    have h := golden_properties.2.2
    dsimp [maximumVarianceMean, goldenRoot] at h ⊢
    nlinarith only [h]
  have hf := variance_factor maximumVarianceMean_mem
  rw [he, Real.sqrt_sq golden_properties.1, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul] at hf
  linarith

/-- Remark 1.8(c): an actual copula attains the bound at x0=(7-3sqrt(5))/4. -/
theorem universal_variance_maximum_attained :
    ∃ C : Copula 2, C.spearmanFootrule = (7 - 3 * Real.sqrt 5) / 4 ∧
      distanceVariance C = 5 * (3 - Real.sqrt 5) / 24 := by
  obtain ⟨C, hm, hv⟩ := maximum_variance_attained maximumVarianceMean_mem
  refine ⟨C, ?_, hv.trans maximumVariance_at_maximizer⟩
  have hp : C.spearmanFootrule = 1 - 3 * meanDistance C := Verification.footrule_eq_abs_moment C
  rw [hp, hm]
  unfold maximumVarianceMean
  ring

end Papers.AnsariRockel2026RhoFootrule
