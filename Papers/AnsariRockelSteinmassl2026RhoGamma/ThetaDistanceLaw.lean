import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaPotential

/-! # The source auxiliary distance law: an atom and a uniform interval component -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

noncomputable def sourceAtomMass (N : ℕ) (delta : ℝ) : ℝ := 1 - 2 * N * (N + 1) * |delta|

private theorem right_distance_law (S : RhoFootrule.RightData) (f : ℝ → ℝ) (hf : Continuous f) :
    let ell := 1 / (2 * (S.N + 1 : ℝ))
    (∫ x, f |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) =
      sourceAtomMass S.N S.v * f ell + (1 - sourceAtomMass S.N S.v) * ∫ u : I, f (ell + S.v * u) := by
  dsimp only
  have hel : 1 / (2 * (S.N + 1 : ℝ)) = S.w + S.N * S.v := by
    apply (div_eq_iff (by positivity : (2 * (S.N + 1 : ℝ)) ≠ 0)).mpr
    nlinarith only [S.normalized]
  rw [hel, S.integral_distance_formula f hf]
  have hp : sourceAtomMass S.N S.v = 2 * (S.N + 1) * S.w := by
    dsimp [sourceAtomMass]
    rw [abs_of_nonneg S.v_nonneg]
    nlinarith only [S.normalized]
  have hpc : 1 - sourceAtomMass S.N S.v = 2 * S.N * (S.N + 1) * S.v := by
    dsimp [sourceAtomMass]
    rw [abs_of_nonneg S.v_nonneg]
    ring
  rw [hpc, hp]

private theorem left_distance_law (S : RhoFootrule.LeftData) (f : ℝ → ℝ) (hf : Continuous f) :
    let ell := 1 / (2 * (S.N : ℝ))
    (∫ x, f |(x 0 : ℝ) - x 1| ∂S.copula.toMeasure) =
      sourceAtomMass S.N (-S.v) * f ell + (1 - sourceAtomMass S.N (-S.v)) * ∫ u : I, f (ell + (-S.v) * u) := by
  dsimp only
  have hn : (0 : ℝ) < S.N := by exact_mod_cast S.N_pos
  have hel : 1 / (2 * (S.N : ℝ)) = S.w + (S.N + 1) * S.v := by
    apply (div_eq_iff (by positivity : (2 * (S.N : ℝ)) ≠ 0)).mpr
    nlinarith only [S.normalized]
  rw [hel, S.integral_distance_formula f hf, ← S.integral_distance_reversed f]
  have hp : sourceAtomMass S.N (-S.v) = 2 * S.N * S.w := by
    dsimp [sourceAtomMass]
    rw [abs_neg, abs_of_nonneg S.v_nonneg]
    nlinarith only [S.normalized]
  have hpc : 1 - sourceAtomMass S.N (-S.v) = 2 * S.N * (S.N + 1) * S.v := by
    dsimp [sourceAtomMass]
    rw [abs_neg, abs_of_nonneg S.v_nonneg]
    ring
  rw [hpc, hp]
  simp only [neg_mul, sub_eq_add_neg]

/-- Section 2.1's complete distance-distribution formula, tested against every continuous function. -/
theorem theta_distance_distribution (theta : ℝ) (ht : 1 < theta) (f : ℝ → ℝ) (hf : Continuous f) :
    let A := thetaCertificate theta (by linarith)
    let p := sourceAtomMass ⌊theta⌋₊ (thetaDelta theta)
    (∫ x, f |(x 0 : ℝ) - x 1| ∂A.D.toMeasure) =
      p * f (thetaEll theta) + (1 - p) * ∫ u : I, f (thetaEll theta + thetaDelta theta * u) := by
  dsimp only
  unfold thetaCertificate
  rw [dite_eq_right (not_le.mpr ht)]
  split
  next hb =>
    have hn : 0 < ⌊theta⌋₊ := Nat.floor_pos.mpr ht.le
    have hupper : 1 / theta ≤ 1 / (⌊theta⌋₊ : ℝ) := one_div_le_one_div_of_le
      (by exact_mod_cast hn) (Nat.floor_le (by linarith))
    have he : thetaDelta theta = -(1 / (⌊theta⌋₊ : ℝ) - 1 / theta) := by
      simp only [thetaDelta, thetaEll, hb, ite_true]
      ring
    have h := left_distance_law (sourceLeft ⌊theta⌋₊ hn (1 / theta) hb hupper) f hf
    simpa only [thetaEll, hb, ite_true, he, RhoGamma.AuxiliaryCertificate.ofLeft, sourceLeft] using h
  next hb =>
    have hn : 0 < ⌊theta⌋₊ := Nat.floor_pos.mpr ht.le
    have hlower : 1 / (⌊theta⌋₊ + 1 : ℝ) ≤ 1 / theta :=
      (one_div_lt_one_div_of_lt (by linarith) (Nat.lt_floor_add_one theta)).le
    have he : thetaDelta theta = 1 / theta - 1 / (⌊theta⌋₊ + 1 : ℝ) := by
      simp only [thetaDelta, thetaEll, hb, ite_false]
      field_simp
    have h := right_distance_law (sourceRight ⌊theta⌋₊ hn (1 / theta) hlower (le_of_not_ge hb)) f hf
    simpa only [thetaEll, hb, ite_false, he, RhoGamma.AuxiliaryCertificate.ofRight, sourceRight] using h

/-- The atom and interval-component weights are genuine probabilities. -/
theorem theta_atom_mass_bounds (theta : ℝ) (ht : 1 < theta) :
    sourceAtomMass ⌊theta⌋₊ (thetaDelta theta) ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : 0 < ⌊theta⌋₊ := Nat.floor_pos.mpr ht.le
  have hnon : 0 ≤ 2 * (⌊theta⌋₊ : ℝ) * (⌊theta⌋₊ + 1) * |thetaDelta theta| := by positivity
  constructor
  · unfold thetaDelta thetaEll sourceAtomMass
    split
    next hb =>
      have hupper : 1 / theta ≤ 1 / (⌊theta⌋₊ : ℝ) := one_div_le_one_div_of_le
        (by exact_mod_cast hn) (Nat.floor_le (by linarith))
      let S := sourceLeft ⌊theta⌋₊ hn (1 / theta) hb hupper
      have hv := S.v_nonneg
      have he : 1 / theta - 2 * (1 / (2 * (⌊theta⌋₊ : ℝ))) = -S.v := by dsimp [S, sourceLeft]; ring
      rw [he, abs_neg, abs_of_nonneg hv]
      have hh := mul_nonneg (show (0 : ℝ) ≤ S.N by positivity) S.w_nonneg
      change 0 ≤ 1 - 2 * S.N * (S.N + 1) * S.v
      nlinarith only [S.normalized, hh]
    next hb =>
      have hlower : 1 / (⌊theta⌋₊ + 1 : ℝ) ≤ 1 / theta :=
        (one_div_lt_one_div_of_lt (by linarith) (Nat.lt_floor_add_one theta)).le
      let S := sourceRight ⌊theta⌋₊ hn (1 / theta) hlower (le_of_not_ge hb)
      have hv := S.v_nonneg
      have he : 1 / theta - 2 * (1 / (2 * (⌊theta⌋₊ + 1 : ℝ))) = S.v := by dsimp [S, sourceRight]; field_simp
      rw [he, abs_of_nonneg hv]
      have hh := mul_nonneg (show (0 : ℝ) ≤ S.N + 1 by positivity) S.w_nonneg
      change 0 ≤ 1 - 2 * S.N * (S.N + 1) * S.v
      nlinarith only [S.normalized, hh]
  · dsimp [sourceAtomMass]
    linarith only [hnon]

/-- The source bound |delta|<=L-R holds uniformly on every finite branch. -/
theorem theta_delta_bound (theta : ℝ) (ht : 1 < theta) :
    |thetaDelta theta| ≤ 1 / (2 * (⌊theta⌋₊ : ℝ)) - 1 / (2 * (⌊theta⌋₊ + 1 : ℝ)) := by
  have hn : (0 : ℝ) < ⌊theta⌋₊ := by exact_mod_cast Nat.floor_pos.mpr ht.le
  have h := (theta_atom_mass_bounds theta ht).1
  dsimp [sourceAtomMass] at h
  have he : 1 / (2 * (⌊theta⌋₊ : ℝ)) - 1 / (2 * (⌊theta⌋₊ + 1 : ℝ)) =
      1 / (2 * (⌊theta⌋₊ : ℝ) * (⌊theta⌋₊ + 1)) := by field_simp; ring
  rw [he]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [h]

/-- At each internal source junction, the atomic part vanishes. -/
theorem theta_midpoint_atom_zero (theta : ℝ) (ht : 1 < theta)
    (hmid : 1 / theta = 1 / (2 * (⌊theta⌋₊ : ℝ)) + 1 / (2 * (⌊theta⌋₊ + 1 : ℝ))) :
    sourceAtomMass ⌊theta⌋₊ (thetaDelta theta) = 0 := by
  have hn : (0 : ℝ) < ⌊theta⌋₊ := by exact_mod_cast Nat.floor_pos.mpr ht.le
  have hlr : 1 / (2 * (⌊theta⌋₊ + 1 : ℝ)) ≤ 1 / (2 * (⌊theta⌋₊ : ℝ)) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hb : 1 / (2 * (⌊theta⌋₊ : ℝ)) + 1 / (2 * (⌊theta⌋₊ + 1 : ℝ)) ≤ 1 / theta := hmid.symm.le
  rw [sourceAtomMass, thetaDelta, thetaEll, ite_eq_left hb, hmid]
  rw [abs_of_nonpos (by linarith)]
  field_simp
  ring

end Papers.AnsariRockelSteinmassl2026RhoGamma
