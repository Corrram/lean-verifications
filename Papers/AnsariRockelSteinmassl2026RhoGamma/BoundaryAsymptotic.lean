import Papers.AnsariRockelSteinmassl2026RhoGamma.GluedEstimates
import Mathlib.Analysis.Asymptotics.Defs

/-! # Remark 2.2: the uniform cubic asymptotic at the comonotone endpoint -/

open MeasureTheory ProbabilityTheory Copula.RankRegion Filter Asymptotics
open scoped unitInterval Topology

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private noncomputable def distanceMean (C : Copula 2) : ℝ := ∫ x, |(x 0 : ℝ) - x 1| ∂C.toMeasure
private noncomputable def distanceSquare (C : Copula 2) : ℝ := ∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂C.toMeasure

private theorem certificate_coordinates (A : RhoGamma.AuxiliaryCertificate) :
    A.copula.giniGamma = 1 - 2 * (A.a : ℝ) ^ 2 - A.z ^ 2 * distanceMean A.D ∧
      A.copula.spearmanRho = 1 - 2 * (A.a : ℝ) ^ 3 - 3 / 2 * A.z ^ 3 * distanceSquare A.D := by
  have hm := RhoFootrule.moment_representation A.D
  rw [A.gamma, A.rho, hm.1, hm.2]
  dsimp [distanceMean, distanceSquare]
  constructor <;> ring

private theorem small_multiplier (A : RhoGamma.AuxiliaryCertificate)
    (hg : 99 / 100 < A.copula.giniGamma) : A.s ≤ 1 / 4 := by
  have hm : 0 ≤ distanceMean A.D := integral_nonneg (fun x => abs_nonneg _)
  have hs := A.s_pos
  have ha := A.a_pos
  have hz := A.z_pos
  have hsum := A.a_add_z
  have hgamma := (certificate_coordinates A).1
  have hnon := mul_nonneg (sq_nonneg A.z) hm
  have haSmall : (A.a : ℝ) < 1 / 10 := by nlinarith only [hg, hgamma, hnon, ha]
  have ht := A.slope_bound
  rw [A.t_eq] at ht
  have hw := mul_nonneg hz.le A.w_nonneg
  have hl := mul_le_mul_of_nonneg_left (show 9 / 10 ≤ A.z by linarith) hs.le
  nlinarith only [ht, hw, hl, haSmall]

private theorem right_estimates (S : RhoFootrule.RightData)
    (hs1 : RhoFootrule.UpperSpline.period S.N S.v S.w ≤ 1) :
    let s := RhoFootrule.UpperSpline.period S.N S.v S.w
    0 ≤ distanceMean S.copula ∧ distanceMean S.copula ≤ s ∧
      |distanceMean S.copula - s / 2| ≤ s ^ 2 / 2 ∧
      |distanceSquare S.copula - s ^ 2 / 4| ≤ 2 * s ^ 3 := by
  have hn : (1 : ℝ) ≤ S.N := by exact_mod_cast S.N_pos
  have hkv : (S.N : ℝ) * (S.N + 1) * S.v ≤ 1 / 2 := by
    nlinarith only [S.normalized, mul_nonneg (show (0 : ℝ) ≤ S.N + 1 by positivity) S.w_nonneg]
  have hns : 1 ≤ (S.N + 1 : ℝ) * RhoFootrule.UpperSpline.period S.N S.v S.w := by
    dsimp [RhoFootrule.UpperSpline.period]
    nlinarith only [S.normalized, mul_nonneg (show (0 : ℝ) ≤ S.N + 1 by positivity) S.v_nonneg]
  have hv := arc_width_bound hn S.v_nonneg S.period_pos.le hkv hns
  have hd := right_source_data S
  dsimp only at hd ⊢
  rw [distanceMean, distanceSquare, hd.2.1, hd.2.2.1]
  have hh := source_moment_estimates (by positivity : 0 ≤ (S.N : ℝ) * (S.N + 1))
    S.period_pos.le hs1 hd.1 (by simpa only [abs_of_nonneg S.v_nonneg] using hv)
    (by simpa only [abs_of_nonneg S.v_nonneg] using hkv)
  dsimp only at hh
  convert hh using 1 <;> dsimp [sourceMean, sourceSquare] <;> ring_nf

private theorem left_estimates (S : RhoFootrule.LeftData)
    (hs1 : RhoFootrule.UpperSpline.period S.N S.v S.w ≤ 1) :
    let s := RhoFootrule.UpperSpline.period S.N S.v S.w
    0 ≤ distanceMean S.copula ∧ distanceMean S.copula ≤ s ∧
      |distanceMean S.copula - s / 2| ≤ s ^ 2 / 2 ∧
      |distanceSquare S.copula - s ^ 2 / 4| ≤ 2 * s ^ 3 := by
  have hn : (1 : ℝ) ≤ S.N := by exact_mod_cast S.N_pos
  have hkv : (S.N : ℝ) * (S.N + 1) * S.v ≤ 1 / 2 := by
    nlinarith only [S.normalized, mul_nonneg (show (0 : ℝ) ≤ S.N by positivity) S.w_nonneg]
  have hns : 1 ≤ (S.N + 1 : ℝ) * RhoFootrule.UpperSpline.period S.N S.v S.w := by
    dsimp [RhoFootrule.UpperSpline.period]
    nlinarith only [S.normalized, S.w_nonneg, mul_nonneg (show (0 : ℝ) ≤ S.N + 1 by positivity) S.v_nonneg]
  have hv := arc_width_bound hn S.v_nonneg S.period_pos.le hkv hns
  have hd := left_source_data S
  dsimp only at hd ⊢
  rw [distanceMean, distanceSquare, hd.2.1, hd.2.2.1]
  have hh := source_moment_estimates (delta := -S.v) (ell := 1 / (2 * (S.N : ℝ)))
    (s := RhoFootrule.UpperSpline.period S.N S.v S.w)
    (by positivity : 0 ≤ (S.N : ℝ) * (S.N + 1)) S.period_pos.le hs1
    (by linarith only [hd.1])
    (by simpa only [abs_neg, abs_of_nonneg S.v_nonneg] using hv)
    (by simpa only [abs_neg, abs_of_nonneg S.v_nonneg] using hkv)
  dsimp only at hh
  convert hh using 1 <;> dsimp [sourceMean, sourceSquare] <;> ring_nf

private theorem certificate_error (A : RhoGamma.AuxiliaryCertificate) (hs1 : A.s ≤ 1 / 4)
    (hm : distanceMean A.D ≤ A.s ∧ |distanceMean A.D - A.s / 2| ≤ A.s ^ 2 / 2 ∧
      |distanceSquare A.D - A.s ^ 2 / 4| ≤ 2 * A.s ^ 3) :
    |A.copula.spearmanRho - (1 - 3 / 2 * (1 - A.copula.giniGamma) ^ 2)| ≤
      98304 * (1 - A.copula.giniGamma) ^ 3 := by
  have has : (A.a : ℝ) ≤ A.s := by
    have hz1 : A.z ≤ 1 := by linarith [A.a_pos, A.a_add_z]
    have hh := mul_le_mul_of_nonneg_right hz1 A.s_pos.le
    have ht := A.a_lt_t
    rw [A.t_eq] at ht
    nlinarith only [hh, ht]
  have h := glued_cubic_estimate A.s_pos.le hs1 A.a_pos.le has
    (show A.z = 1 - (A.a : ℝ) by linarith [A.a_add_z])
    (show 0 ≤ distanceMean A.D by exact integral_nonneg (fun x => abs_nonneg _)) hm.1
    (show 0 ≤ distanceSquare A.D by exact integral_nonneg (fun x => sq_nonneg _)) hm.2.1 hm.2.2
  dsimp only at h
  rw [(certificate_coordinates A).1, (certificate_coordinates A).2]
  convert h.2 using 1
  · rw [show 1 - 2 * (A.a : ℝ) ^ 3 - 3 / 2 * A.z ^ 3 * distanceSquare A.D -
        (1 - 3 / 2 * (1 - (1 - 2 * (A.a : ℝ) ^ 2 - A.z ^ 2 * distanceMean A.D)) ^ 2) =
      -(2 * (A.a : ℝ) ^ 3 + 3 / 2 * A.z ^ 3 * distanceSquare A.D -
        3 / 2 * (2 * (A.a : ℝ) ^ 2 + A.z ^ 2 * distanceMean A.D) ^ 2) by ring, abs_neg]
  · ring

/-- A single explicit remainder constant works on every arc near gamma=1. -/
theorem upper_boundary_cubic_remainder {g : ℝ} (hg : 99 / 100 < g) (hg1 : g < 1) :
    |upperRho g - (1 - 3 / 2 * (1 - g) ^ 2)| ≤ 98304 * (1 - g) ^ 3 := by
  obtain ⟨p, hp⟩ := RhoGamma.upperParameter_exists (show g ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> linarith)
  rw [← hp, upperRho_parameter]
  cases p with
  | lowerEndpoint => change (-1 : ℝ) = g at hp; linarith
  | upperEndpoint => change (1 : ℝ) = g at hp; linarith
  | halfShift s hs =>
    have hc : 99 / 100 < (RhoGamma.AuxiliaryCertificate.halfShift s hs).copula.giniGamma := by
      change 99 / 100 < (RhoGamma.UpperParameter.halfShift s hs).copula.giniGamma
      rw [(RhoGamma.UpperParameter.halfShift s hs).gamma_coefficient, hp]
      exact hg
    have hh := small_multiplier _ hc
    change s ≤ 1 / 4 at hh
    linarith
  | right S =>
    have hc : 99 / 100 < (RhoGamma.AuxiliaryCertificate.ofRight S).copula.giniGamma := by
      change 99 / 100 < (RhoGamma.UpperParameter.right S).copula.giniGamma
      rw [(RhoGamma.UpperParameter.right S).gamma_coefficient, hp]
      exact hg
    have hs := small_multiplier _ hc
    have hm := right_estimates S (by change RhoFootrule.UpperSpline.period S.N S.v S.w ≤ 1 / 4 at hs; linarith)
    have he := certificate_error (RhoGamma.AuxiliaryCertificate.ofRight S) hs hm.2
    rw [← (RhoGamma.UpperParameter.right S).gamma_coefficient, ← (RhoGamma.UpperParameter.right S).rho_coefficient]
    exact he
  | left S =>
    have hc : 99 / 100 < (RhoGamma.AuxiliaryCertificate.ofLeft S).copula.giniGamma := by
      change 99 / 100 < (RhoGamma.UpperParameter.left S).copula.giniGamma
      rw [(RhoGamma.UpperParameter.left S).gamma_coefficient, hp]
      exact hg
    have hs := small_multiplier _ hc
    have hm := left_estimates S (by change RhoFootrule.UpperSpline.period S.N S.v S.w ≤ 1 / 4 at hs; linarith)
    have he := certificate_error (RhoGamma.AuxiliaryCertificate.ofLeft S) hs hm.2
    rw [← (RhoGamma.UpperParameter.left S).gamma_coefficient, ← (RhoGamma.UpperParameter.left S).rho_coefficient]
    exact he

/-- Equation (23), with the limit taken from below at gamma=1. -/
theorem upper_boundary_asymptotic :
    (fun g : ℝ => upperRho g - (1 - 3 / 2 * (1 - g) ^ 2))
      =O[nhdsWithin 1 (Set.Iio 1)] (fun g : ℝ => (1 - g) ^ 3) := by
  apply IsBigO.of_bound 98304
  have hlo : ∀ᶠ g : ℝ in nhdsWithin 1 (Set.Iio 1), 99 / 100 < g :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (99 : ℝ) / 100 < 1))
  filter_upwards [hlo, self_mem_nhdsWithin] with g hg hg1
  change g < 1 at hg1
  have h := upper_boundary_cubic_remainder hg hg1
  have hp : 0 ≤ (1 - g) ^ 3 := pow_nonneg (sub_nonneg.mpr hg1.le) 3
  simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using h

end Papers.AnsariRockelSteinmassl2026RhoGamma
