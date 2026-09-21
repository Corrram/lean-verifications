import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaContinuity
import Papers.AnsariRockelSteinmassl2026RhoGamma.BoundaryGeometry

/-! # Both limiting endpoints and full coverage of the source theta parametrization -/

open MeasureTheory ProbabilityTheory Copula.RankRegion Set Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private theorem right_mean_bound (S : RhoFootrule.RightData) :
    (∫ x, |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) ≤ RhoFootrule.UpperSpline.period S.N S.v S.w := by
  have hkv : (S.N : ℝ) * (S.N + 1) * S.v ≤ 1 / 2 := by
    nlinarith only [S.normalized, mul_nonneg (show (0 : ℝ) ≤ S.N + 1 by positivity) S.w_nonneg]
  have hh := mul_le_mul_of_nonneg_right hkv S.v_nonneg
  have hn := mul_nonneg (Nat.cast_nonneg S.N : (0 : ℝ) ≤ S.N) S.v_nonneg
  rw [S.integral_abs_distance]
  dsimp [RhoFootrule.UpperSpline.period]
  nlinarith only [hh, hn, S.w_nonneg, S.v_nonneg]

private theorem left_mean_bound (S : RhoFootrule.LeftData) :
    (∫ x, |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) ≤ RhoFootrule.UpperSpline.period S.N S.v S.w := by
  have hn := mul_nonneg (Nat.cast_nonneg S.N : (0 : ℝ) ≤ S.N) S.v_nonneg
  have hq : 0 ≤ (S.N : ℝ) * (S.N + 1) * S.v ^ 2 := by positivity
  rw [S.integral_abs_distance]
  dsimp [RhoFootrule.UpperSpline.period]
  nlinarith only [hn, hq, S.w_nonneg]

private theorem thetaMean_bound (theta : ℝ) (ht : 0 < theta) :
    0 ≤ thetaMean theta ∧ thetaMean theta ≤ 1 / theta := by
  constructor
  · rw [← (thetaCertificate_data theta ht).1]
    exact integral_nonneg (fun x => abs_nonneg _)
  · rw [← (thetaCertificate_data theta ht).1, ← thetaCertificate_s theta ht]
    unfold thetaCertificate
    split
    next h =>
      change (∫ x, |(x 0 : ℝ) - x 1| ∂RhoFootrule.halfTurn.toMeasure) ≤ 1 / theta
      have hm := (RhoFootrule.moment_representation RhoFootrule.halfTurn).2
      rw [RhoFootrule.halfTurn_footrule] at hm
      have hi : 1 ≤ 1 / theta := (le_div_iff₀ ht).mpr (by simpa using h)
      linarith
    · split
      · exact left_mean_bound _
      · exact right_mean_bound _

private theorem thetaG_mem (theta : ℝ) (ht : 0 < theta) : thetaG theta ∈ Icc (-1 : ℝ) 1 :=
  (theta_boundary_coefficients theta ht).1 ▸ (thetaCertificate theta ht).copula.giniGamma_mem_Icc

private theorem theta_gamma_error (theta : ℝ) (ht : 0 < theta) :
    0 ≤ 1 - thetaG theta ∧ 1 - thetaG theta ≤ 2 * (1 / theta) ^ 2 + 1 / theta := by
  let A := thetaCertificate theta ht
  have hs := theta_splitting theta ht
  dsimp only at hs
  have ha := A.a_pos
  have hz := A.z_pos
  have hsum := A.a_add_z
  have hz1 : A.z ≤ 1 := by linarith
  have has : (A.a : ℝ) ≤ 1 / theta := by
    have hh := mul_le_mul_of_nonneg_right hz1 A.s_pos.le
    have hh' := A.a_lt_t
    rw [A.t_eq] at hh'
    have he : A.s = 1 / theta := thetaCertificate_s theta ht
    rw [he] at hh hh'
    nlinarith only [hh, hh']
  have hms := thetaMean_bound theta ht
  have hzsq : A.z ^ 2 ≤ 1 := by nlinarith
  have hmz := mul_le_mul_of_nonneg_right hzsq hms.1
  have hasq : (A.a : ℝ) ^ 2 ≤ (1 / theta) ^ 2 := by nlinarith [div_pos zero_lt_one ht]
  rw [thetaG, ← hs.2.2.1, ← hs.2.2.2]
  change 0 ≤ 1 - (1 - 2 * (A.a : ℝ) ^ 2 - A.z ^ 2 * thetaMean theta) ∧ _
  constructor
  · nlinarith only [sq_nonneg (A.a : ℝ), mul_nonneg (sq_nonneg A.z) hms.1]
  · nlinarith only [hmz, hasq, hms.2]

/-- The gamma coordinate tends to one along the full source family. -/
theorem thetaG_tendsto_atTop : Tendsto thetaG atTop (nhds 1) := by
  have hi : Tendsto (fun theta : ℝ => 1 / theta) atTop (nhds 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0))
  have hbound : Tendsto (fun theta : ℝ => 2 * (1 / theta) ^ 2 + 1 / theta) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (hi.pow 2)).add hi
  have he : ∀ᶠ theta : ℝ in atTop, 0 ≤ 1 - thetaG theta ∧
      1 - thetaG theta ≤ 2 * (1 / theta) ^ 2 + 1 / theta := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with theta ht
    exact theta_gamma_error theta ht
  have h := squeeze_zero' (he.mono fun _ h => h.1) (he.mono fun _ h => h.2) hbound
  have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  simpa only [sub_zero, sub_sub_cancel] using h1.sub h

/-- The gamma coordinate tends to minus one as theta decreases to zero. -/
theorem thetaG_tendsto_zero : Tendsto thetaG (nhdsWithin 0 (Ioi 0)) (nhds (-1)) := by
  have hpos : ∀ᶠ theta : ℝ in nhdsWithin 0 (Ioi 0), 0 < theta := self_mem_nhdsWithin
  have hsmall : ∀ᶠ theta : ℝ in nhdsWithin 0 (Ioi 0), theta < 1 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have he : ∀ᶠ theta : ℝ in nhdsWithin 0 (Ioi 0), 0 ≤ thetaG theta + 1 ∧ thetaG theta + 1 ≤ 8 * theta := by
    filter_upwards [hpos, hsmall] with theta ht ht1
    have hi : 1 ≤ 1 / theta := (le_div_iff₀ ht).mpr (by linarith)
    have hc : thetaG theta = RhoGamma.gammaValue (1 / theta) (3 / 8 - (1 / theta) / 2) (1 / 2) := by
      rw [← (theta_boundary_coefficients theta ht).1]
      unfold thetaCertificate
      rw [dite_eq_left ht1.le]
      exact (RhoGamma.UpperParameter.halfShift (1 / theta) hi).gamma_coefficient
    have hh := RhoGamma.halfShift_near_endpoint hi
    rw [← hc] at hh
    have hl := (thetaG_mem theta ht).1
    have hd : 8 / (1 / theta) = 8 * theta := by field_simp
    rw [hd] at hh
    constructor <;> linarith
  have hbound : Tendsto (fun theta : ℝ => 8 * theta) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun theta : ℝ => 8 * theta) (nhdsWithin 0 (Ioi 0)) (nhds (8 * 0)))
  have h := squeeze_zero' (he.mono fun _ h => h.1) (he.mono fun _ h => h.2) hbound
  simpa using h.sub_const 1

private theorem thetaP_limit {l : Filter ℝ} {g : ℝ} (hpos : ∀ᶠ theta : ℝ in l, 0 < theta)
    (hG : Tendsto thetaG l (nhds g)) (hg : g ∈ Icc (-1 : ℝ) 1) :
    Tendsto thetaP l (nhds (upperRho g)) := by
  have hG' : Tendsto thetaG l (nhdsWithin g (Icc (-1 : ℝ) 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hG, hpos.mono fun theta ht => thetaG_mem theta ht⟩
  have hp := (upperRho_continuous g hg).tendsto.comp hG'
  apply hp.congr'
  filter_upwards [hpos] with theta ht
  exact theta_boundary_value theta ht

/-- The full coordinate pair tends to the comonotone endpoint (1,1). -/
theorem theta_coordinates_tendsto_atTop :
    Tendsto (fun theta : ℝ => (thetaG theta, thetaP theta)) atTop (nhds (1, 1)) := by
  have hp := thetaP_limit (eventually_gt_atTop (0 : ℝ)) thetaG_tendsto_atTop (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)
  rw [upperRho_endpoints.2] at hp
  exact thetaG_tendsto_atTop.prodMk_nhds hp

/-- The full coordinate pair tends to the countermonotone endpoint (-1,-1). -/
theorem theta_coordinates_tendsto_zero :
    Tendsto (fun theta : ℝ => (thetaG theta, thetaP theta)) (nhdsWithin 0 (Ioi 0)) (nhds (-1, -1)) := by
  have hp := thetaP_limit self_mem_nhdsWithin thetaG_tendsto_zero (by norm_num : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1)
  rw [upperRho_endpoints.1] at hp
  exact thetaG_tendsto_zero.prodMk_nhds hp

/-- Every nonendpoint gamma value occurs at a positive finite source theta. -/
theorem theta_gamma_coverage {g : ℝ} (hg : -1 < g) (hg1 : g < 1) :
    ∃ theta : ℝ, 0 < theta ∧ thetaG theta = g := by
  have hl : ∀ᶠ theta : ℝ in nhdsWithin 0 (Ioi 0), thetaG theta < g :=
    thetaG_tendsto_zero.eventually (gt_mem_nhds hg)
  have hu : ∀ᶠ theta : ℝ in atTop, g < thetaG theta :=
    thetaG_tendsto_atTop.eventually (lt_mem_nhds hg1)
  obtain ⟨a, ha, hap⟩ := (hl.and self_mem_nhdsWithin).exists
  obtain ⟨b, hb, hbp⟩ := (hu.and (eventually_gt_atTop (0 : ℝ))).exists
  have hc : ContinuousOn thetaG (Ioi (0 : ℝ)) := continuous_theta_coordinates.fst
  exact isPreconnected_Ioi.intermediate_value hap hbp hc ⟨ha.le, hb.le⟩

/-- The source endpoint convention at theta=0 is also the value of the explicit formulas. -/
theorem theta_coordinates_zero : (thetaG 0, thetaP 0) = (-1, -1) := by
  norm_num [thetaG, thetaP, thetaA, thetaZ, thetaT, thetaAlpha, thetaOffset,
    thetaMean, thetaSquare]

/-- Continuity on all finite nonnegative theta, including the endpoint zero. -/
theorem continuous_theta_coordinates_nonnegative :
    ContinuousOn (fun theta : ℝ => (thetaG theta, thetaP theta)) (Ici 0) := by
  intro theta htheta
  by_cases h0 : theta = 0
  · subst theta
    apply continuousWithinAt_Ioi_iff_Ici.mp
    change Tendsto (fun theta : ℝ => (thetaG theta, thetaP theta)) (nhdsWithin 0 (Ioi 0))
      (nhds (thetaG 0, thetaP 0))
    rw [theta_coordinates_zero]
    exact theta_coordinates_tendsto_zero
  · have ht : 0 < theta := lt_of_le_of_ne htheta (Ne.symm h0)
    exact (continuous_theta_coordinates theta ht).continuousAt (Ioi_mem_nhds ht) |>.continuousWithinAt

/-- Theorem 1.1's surjectivity, including both endpoint conventions. -/
theorem theta_gamma_full_range (g : ℝ) :
    g ∈ Icc (-1 : ℝ) 1 ↔ g = -1 ∨ g = 1 ∨ ∃ theta : ℝ, 0 < theta ∧ thetaG theta = g := by
  constructor
  · intro hg
    by_cases hl : g = -1
    · exact Or.inl hl
    by_cases hu : g = 1
    · exact Or.inr (Or.inl hu)
    exact Or.inr (Or.inr (theta_gamma_coverage (lt_of_le_of_ne hg.1 (Ne.symm hl)) (lt_of_le_of_ne hg.2 hu)))
  · rintro (rfl | rfl | ⟨theta, ht, rfl⟩)
    · norm_num
    · norm_num
    · exact thetaG_mem theta ht

end Papers.AnsariRockelSteinmassl2026RhoGamma
