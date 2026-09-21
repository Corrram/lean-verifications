import Papers.AnsariRockelSteinmassl2026RhoGamma.ShuffleGraph

/-! # The exact endpoint and complete d-coverage of Example 3.10 -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

noncomputable def elementaryDStar : ℝ := (12 - 2 * Real.sqrt 3) / 33
noncomputable def elementaryGStar : ℝ := (173 - 16 * Real.sqrt 3) / 363

/-- Equation (20): the elementary arc ends at the source's explicit radical constants. -/
theorem elementary_endpoint_constants :
    (RhoGamma.AuxiliaryCertificate.halfShift 1 (by norm_num)).z / 2 = elementaryDStar ∧
      RhoGamma.contactGamma 1 = elementaryGStar := by
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hd : (6 : ℝ) + Real.sqrt 3 ≠ 0 := by positivity
  dsimp [RhoGamma.AuxiliaryCertificate.z, RhoGamma.AuxiliaryCertificate.halfShift,
    RhoGamma.contactGamma, RhoGamma.gammaValue, RhoGamma.centralLength,
    RhoGamma.cornerLength, RhoGamma.splitRatio, elementaryDStar, elementaryGStar]
  norm_num
  constructor
  · field_simp
    nlinarith only [hsq]
  · field_simp
    nlinarith only [hsq, congrArg (fun r : ℝ => r * Real.sqrt 3) hsq]

/-- Every positive corner size through d-star occurs in the half-shift family. -/
theorem elementary_d_coverage {d : ℝ} (hd : 0 < d) (hdstar : d ≤ elementaryDStar) :
    ∃ s : ℝ, ∃ hs : 1 ≤ s, (RhoGamma.AuxiliaryCertificate.halfShift s hs).z / 2 = d := by
  let S : ℝ := 1 + 2 / d
  have hS : 1 ≤ S := by dsimp [S]; linarith [div_pos (by norm_num : (0 : ℝ) < 2) hd]
  have hSp : 0 < S := by linarith
  have hsmall : 1 / S < d := by
    apply (div_lt_iff₀ hSp).mpr
    have he : d * S = d + 2 := by dsimp [S]; field_simp
    linarith
  let scale : I → ℝ := fun u => S + (1 - S) * u
  have hscale (u : I) : 1 ≤ scale u := by
    have h := mul_nonneg (show 0 ≤ S - 1 by linarith) (sub_nonneg.mpr u.property.2)
    dsimp [scale]
    nlinarith
  have hden (u : I) : 1 + RhoGamma.splitRatio (scale u) (3 / 8 - scale u / 2) ≠ 0 := by
    unfold RhoGamma.splitRatio
    have hn := Real.sqrt_nonneg ((scale u) ^ 2 + 2 * (3 / 8 - scale u / 2))
    linarith [hscale u]
  have hc : Continuous (fun u : I => RhoGamma.cornerLength (scale u) (3 / 8 - scale u / 2) / 2) := by
    unfold RhoGamma.cornerLength
    apply Continuous.div_const
    apply Continuous.div continuous_const _ hden
    dsimp [RhoGamma.splitRatio, scale]
    fun_prop
  obtain ⟨u, hu⟩ := exists_unitInterval_eq hc
    (show RhoGamma.cornerLength (scale 0) (3 / 8 - scale 0 / 2) / 2 ≤ d by
      have hh := RhoGamma.cornerLength_le_two_div hSp (3 / 8 - S / 2)
      rw [show 2 / S = 2 * (1 / S) by ring] at hh
      dsimp [scale]
      norm_num
      have hbound : RhoGamma.cornerLength S (3 / 8 - S / 2) / 2 ≤ d := by linarith
      exact hbound)
    (by
      have he : scale 1 = 1 := by dsimp [scale]; norm_num
      rw [he]
      exact elementary_endpoint_constants.1 ▸ hdstar)
  exact ⟨scale u, hscale u, hu⟩

/-- Example 3.10, all d in its stated range: graph law and both exact coefficients. -/
theorem five_piece_shuffle_realizes_boundary {d : ℝ} (hd : 0 < d) (hdstar : d ≤ elementaryDStar)
    (hdi : d ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ∃ C : Copula 2,
      C.toMeasure = volume.map (fun u : I => ![u, fivePieceMap d hdi u]) ∧
      C.giniGamma = -1 + 8 * d - 10 * d ^ 2 ∧
      C.spearmanRho = -1 + 12 * d - 24 * d ^ 2 + 13 * d ^ 3 := by
  obtain ⟨s, hs, he⟩ := elementary_d_coverage hd hdstar
  let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
  have hA : A.z / 2 ∈ Set.Icc (0 : ℝ) (1 / 2) := he ▸ hdi
  refine ⟨A.copula, ?_, ?_⟩
  · simpa only [he] using elementary_shuffle_law hs hA
  · have hc := halfShift_arc_coefficients hs
    dsimp only at hc
    simpa only [he] using hc

end Papers.AnsariRockelSteinmassl2026RhoGamma
