import Papers.AnsariRockelSteinmassl2026RhoGamma.SourceBranches

/-! # The original theta-indexed auxiliary and boundary family -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

private theorem theta_index_pos {theta : ℝ} (ht : 1 < theta) : 0 < ⌊theta⌋₊ :=
  Nat.floor_pos.mpr ht.le

private theorem theta_lower {theta : ℝ} (ht : 0 < theta) :
    1 / (⌊theta⌋₊ + 1 : ℝ) ≤ 1 / theta :=
  (one_div_lt_one_div_of_lt ht (Nat.lt_floor_add_one theta)).le

private theorem theta_upper {theta : ℝ} (ht : 1 < theta) :
    1 / theta ≤ 1 / (⌊theta⌋₊ : ℝ) := by
  have hn : (0 : ℝ) < ⌊theta⌋₊ := by exact_mod_cast theta_index_pos ht
  exact one_div_le_one_div_of_le hn (Nat.floor_le (by linarith))

/-- Lemma 3.5's actual primal-dual certificate, with precisely the source branch selection. -/
noncomputable def thetaCertificate (theta : ℝ) (ht : 0 < theta) : RhoGamma.AuxiliaryCertificate :=
  if h : theta ≤ 1 then
    .halfShift (1 / theta) ((le_div_iff₀ ht).mpr (by simpa using h))
  else
    if hb : 1 / (2 * (⌊theta⌋₊ : ℝ)) + 1 / (2 * (⌊theta⌋₊ + 1 : ℝ)) ≤ 1 / theta then
      .ofLeft (sourceLeft ⌊theta⌋₊ (theta_index_pos (lt_of_not_ge h)) (1 / theta) hb (theta_upper (lt_of_not_ge h)))
    else
      .ofRight (sourceRight ⌊theta⌋₊ (theta_index_pos (lt_of_not_ge h)) (1 / theta)
        (theta_lower ht) (le_of_not_ge hb))

/-- Equation (16)'s choice of the contact distance. -/
noncomputable def thetaEll (theta : ℝ) : ℝ :=
  if 1 / (2 * (⌊theta⌋₊ : ℝ)) + 1 / (2 * (⌊theta⌋₊ + 1 : ℝ)) ≤ 1 / theta
  then 1 / (2 * (⌊theta⌋₊ : ℝ)) else 1 / (2 * (⌊theta⌋₊ + 1 : ℝ))

noncomputable def thetaDelta (theta : ℝ) : ℝ := 1 / theta - 2 * thetaEll theta

noncomputable def thetaMean (theta : ℝ) : ℝ :=
  if theta ≤ 1 then 1 / 2 else sourceMean ⌊theta⌋₊ (thetaEll theta) (thetaDelta theta)

noncomputable def thetaSquare (theta : ℝ) : ℝ :=
  if theta ≤ 1 then 1 / 4 else sourceSquare ⌊theta⌋₊ (thetaEll theta) (thetaDelta theta)

noncomputable def thetaOffset (theta : ℝ) : ℝ :=
  if theta ≤ 1 then 3 / 8 - (1 / theta) / 2
  else sourceOffset ⌊theta⌋₊ (thetaEll theta) (thetaDelta theta)

/-- The auxiliary multiplier really is 1/theta, on all branches. -/
theorem thetaCertificate_s (theta : ℝ) (ht : 0 < theta) :
    (thetaCertificate theta ht).s = 1 / theta := by
  unfold thetaCertificate
  split
  · rfl
  · split
    · dsimp [RhoGamma.AuxiliaryCertificate.ofLeft, sourceLeft, RhoFootrule.UpperSpline.period]
      ring
    · dsimp [RhoGamma.AuxiliaryCertificate.ofRight, sourceRight, RhoFootrule.UpperSpline.period]
      field_simp
      ring

/-- Equation (15) or (17), including the potential normalization, for every theta>0. -/
theorem thetaCertificate_data (theta : ℝ) (ht : 0 < theta) :
    let A := thetaCertificate theta ht
    (∫ x, |(x 0 : ℝ) - x 1| ∂A.D.toMeasure) = thetaMean theta ∧
      (∫ x, ((x 0 : ℝ) - x 1) ^ 2 ∂A.D.toMeasure) = thetaSquare theta ∧
      A.c = thetaOffset theta := by
  dsimp only
  unfold thetaCertificate
  split
  next h =>
    dsimp [RhoGamma.AuxiliaryCertificate.halfShift]
    simp only [thetaMean, thetaSquare, thetaOffset, h, ite_true]
    have hm := RhoFootrule.moment_representation RhoFootrule.halfTurn
    rw [RhoFootrule.halfTurn_footrule, RhoFootrule.halfTurn_rho] at hm
    exact ⟨by linarith [hm.2], by linarith [hm.1], trivial⟩
  next h =>
    simp only [thetaMean, thetaSquare, thetaOffset, h, ite_false]
    split
    next hb =>
      have hd := left_source_data (sourceLeft ⌊theta⌋₊ (theta_index_pos (lt_of_not_ge h)) (1 / theta) hb (theta_upper (lt_of_not_ge h)))
      dsimp only at hd
      have he : thetaDelta theta = -(1 / (⌊theta⌋₊ : ℝ) - 1 / theta) := by
        simp only [thetaDelta, thetaEll, hb, ite_true]
        ring
      simpa only [thetaEll, hb, ite_true, he, sourceLeft, RhoGamma.AuxiliaryCertificate.ofLeft] using hd.2
    next hb =>
      have hd := right_source_data (sourceRight ⌊theta⌋₊ (theta_index_pos (lt_of_not_ge h)) (1 / theta) (theta_lower ht) (le_of_not_ge hb))
      dsimp only at hd
      have he : thetaDelta theta = 1 / theta - 1 / (⌊theta⌋₊ + 1 : ℝ) := by
        simp only [thetaDelta, thetaEll, hb, ite_false]
        field_simp
      simpa only [thetaEll, hb, ite_false, he, sourceRight, RhoGamma.AuxiliaryCertificate.ofRight] using hd.2

/-- The paper's theta and the certificate normalization coincide exactly. -/
theorem sourceTheta_thetaCertificate (theta : ℝ) (ht : 0 < theta) :
    sourceTheta (thetaCertificate theta ht) = theta := by
  unfold sourceTheta
  rw [thetaCertificate_s]
  simp

end Papers.AnsariRockelSteinmassl2026RhoGamma
