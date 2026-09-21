import Papers.AnsariRockelSteinmassl2026RhoGamma.ExactRegion

/-! # The elementary boundary arc and the exact half-shift regime -/

open MeasureTheory ProbabilityTheory Set
open Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

/-- The source's polynomial elementary arc, with d equal to half the corner length. -/
theorem halfShift_arc_coefficients {s : ℝ} (hs : 1 ≤ s) :
    let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
    let d := A.z / 2
    A.copula.giniGamma = -1 + 8 * d - 10 * d ^ 2 ∧
    A.copula.spearmanRho = -1 + 12 * d - 24 * d ^ 2 + 13 * d ^ 3 := by
  dsimp only
  let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
  have ha : (A.a : ℝ) = 1 - A.z := by linarith only [A.a_add_z]
  have hg := A.gamma
  have hr := A.rho
  change A.copula.giniGamma = _ at hg
  have hD : A.D = RhoFootrule.halfTurn := rfl
  rw [hD, RhoFootrule.halfTurn_footrule, ha] at hg
  rw [hD, RhoFootrule.halfTurn_rho, ha] at hr
  constructor
  · rw [hg]; ring
  · rw [hr]; ring

private theorem elementary_polynomial_elimination {d : ℝ} (hd : d ≤ 1 / 3) :
    -1 + 12 * d - 24 * d ^ 2 + 13 * d ^ 3 =
      (144 + 420 * (-1 + 8 * d - 10 * d ^ 2) +
        (9 + 65 * (-1 + 8 * d - 10 * d ^ 2)) *
          Real.sqrt (6 - 10 * (-1 + 8 * d - 10 * d ^ 2))) / 500 := by
  have he : 6 - 10 * (-1 + 8 * d - 10 * d ^ 2) = (4 - 10 * d) ^ 2 := by ring
  rw [he, Real.sqrt_sq (by linarith)]
  ring

/-- Corollary 2.1's radical formula at every elementary-arc parameter. -/
theorem halfShift_arc_closed {s : ℝ} (hs : 1 ≤ s) :
    let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
    let g := A.copula.giniGamma
    A.copula.spearmanRho = (144 + 420 * g + (9 + 65 * g) * Real.sqrt (6 - 10 * g)) / 500 := by
  dsimp only
  let A := RhoGamma.AuxiliaryCertificate.halfShift s hs
  have hz : A.z ≤ 2 / 3 := by
    have hroot := Real.sqrt_nonneg (s ^ 2 + 2 * (3 / 8 - s / 2))
    change 1 / (1 + (s + Real.sqrt (s ^ 2 + 2 * (3 / 8 - s / 2))) / 2) ≤ _
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  rw [(halfShift_arc_coefficients hs).1, (halfShift_arc_coefficients hs).2]
  exact elementary_polynomial_elimination (by change A.z / 2 ≤ 1 / 3; linarith)

/-- Every gamma below the first contact, apart from W, has a half-shift parameter. -/
theorem elementary_arc_coverage {g : ℝ} (hg : -1 < g) (hhi : g ≤ RhoGamma.contactGamma 1) :
    ∃ s : ℝ, ∃ hs : 1 ≤ s,
      (RhoGamma.UpperParameter.halfShift s hs).gamma = g := by
  let S : ℝ := 1 + 16 / (g + 1)
  have hgpos : 0 < g + 1 := by linarith
  have hS : 1 ≤ S := by
    have hh : 0 ≤ 16 / (g + 1) := by positivity
    dsimp [S]; linarith
  have hSp : 0 < S := by linarith
  have hsmall : -1 + 8 / S < g := by
    have he : (g + 1) * S = g + 1 + 16 := by dsimp [S]; field_simp
    have hh : 8 / S < g + 1 := (div_lt_iff₀ hSp).mpr (by nlinarith only [he, hgpos])
    linarith
  let scale : I → ℝ := fun u => S + (1 - S) * u
  have hscale (u : I) : 1 ≤ scale u := by
    have hh := mul_nonneg (show 0 ≤ S - 1 by linarith) (sub_nonneg.mpr u.property.2)
    dsimp [scale]; nlinarith only [hh]
  have hc : Continuous (fun u : I => RhoGamma.gammaValue (scale u) (3 / 8 - scale u / 2) (1 / 2)) :=
    RhoGamma.continuous_gammaValue (by dsimp [scale]; fun_prop) (by dsimp [scale]; fun_prop)
      continuous_const (fun u => by linarith [hscale u])
  have hend : scale 1 = 1 := by dsimp [scale]; norm_num
  obtain ⟨u, hu⟩ := Copula.RankRegion.exists_unitInterval_eq hc
    (by
      have hh := (RhoGamma.halfShift_near_endpoint hS).trans hsmall.le
      simpa [scale] using hh)
    (by simpa only [hend, RhoGamma.halfShift_join] using hhi)
  exact ⟨scale u, hscale u, hu⟩

/-- Corollary 2.1: the closed formula on the whole elementary gamma interval. -/
theorem elementary_upper_boundary {g : ℝ}
    (hg : g ∈ Icc (-1) (RhoGamma.contactGamma 1)) :
    upperRho g = (144 + 420 * g + (9 + 65 * g) * Real.sqrt (6 - 10 * g)) / 500 := by
  by_cases he : g = -1
  · subst g
    rw [show upperRho (-1) = -1 from upperRho_parameter .lowerEndpoint]
    norm_num
  obtain ⟨s, hs, hgamma⟩ := elementary_arc_coverage (lt_of_le_of_ne hg.1 (Ne.symm he)) hg.2
  have hp := upperRho_parameter (.halfShift s hs)
  have hcoeff := (RhoGamma.UpperParameter.halfShift s hs).gamma_coefficient
  have hr := (RhoGamma.UpperParameter.halfShift s hs).rho_coefficient
  have hc := halfShift_arc_closed hs
  dsimp only at hc
  change (RhoGamma.AuxiliaryCertificate.halfShift s hs).copula.giniGamma = _ at hcoeff
  change (RhoGamma.AuxiliaryCertificate.halfShift s hs).copula.spearmanRho = _ at hr
  rw [hcoeff, hr, hgamma] at hc
  rw [hgamma, hc] at hp
  exact hp

/-- An explicit competing copula improves the half-shift cost whenever 0<s<1. -/
theorem halfShift_not_optimal {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    ∃ C : Copula 2,
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1| ∂C.toMeasure) <
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1| ∂RhoFootrule.halfTurn.toMeasure) := by
  let S : RhoFootrule.LeftData :=
    { N := 1, N_pos := by decide, v := (1 - s) / 4, w := s / 2,
      v_nonneg := by positivity, w_nonneg := by positivity,
      normalized := by norm_num; ring }
  refine ⟨S.copula, ?_⟩
  rw [RhoGamma.halfShift_cost,
    integral_sub (Copula.integrable_continuous_cube _ (by fun_prop))
      (Copula.integrable_continuous_cube _ (by fun_prop)), integral_const_mul,
    S.integral_sq_distance, S.integral_abs_distance]
  have he : (S.w + (S.N + 1) * S.v) = 1 / 2 := by dsimp [S]; norm_num; ring
  rw [he]
  have hv : 0 < (1 - s) ^ 3 := pow_pos (by linarith) _
  dsimp [S]
  norm_num
  nlinarith only [hv]

/-- Lemma 3.6 in both directions, with s=1/theta. -/
theorem halfShift_optimal_iff {s : ℝ} (hs : 0 < s) :
    (∀ C : Copula 2,
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1| ∂RhoFootrule.halfTurn.toMeasure) ≤
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 - s * |(x 0 : ℝ) - x 1| ∂C.toMeasure)) ↔ 1 ≤ s := by
  constructor
  · intro h
    by_contra hnot
    obtain ⟨C, hC⟩ := halfShift_not_optimal hs (lt_of_not_ge hnot)
    exact (not_lt_of_ge (h C)) hC
  · exact RhoGamma.halfShift_optimal

end Papers.AnsariRockelSteinmassl2026RhoGamma
