import Papers.AnsariRockelSteinmassl2026RhoGamma.ThetaFamily

/-! # Theorem 1.1 and Proposition 3.9 in the paper's original theta coordinates -/

open MeasureTheory ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

noncomputable def thetaAlpha (theta : ℝ) : ℝ :=
  (1 + Real.sqrt (1 + 2 * theta ^ 2 * thetaOffset theta)) / 2

noncomputable def thetaT (theta : ℝ) : ℝ := 1 / (theta + thetaAlpha theta)
noncomputable def thetaA (theta : ℝ) : ℝ := thetaAlpha theta * thetaT theta
noncomputable def thetaZ (theta : ℝ) : ℝ := theta * thetaT theta

/-- Equation (19), the source gamma coordinate. -/
noncomputable def thetaG (theta : ℝ) : ℝ :=
  1 - 2 * (thetaA theta) ^ 2 - (thetaZ theta) ^ 2 * thetaMean theta

/-- Equation (19), the source rho coordinate. -/
noncomputable def thetaP (theta : ℝ) : ℝ :=
  1 - 2 * (thetaA theta) ^ 3 - 3 / 2 * (thetaZ theta) ^ 3 * thetaSquare theta

/-- The source formulas (18) agree with the actual copula's gluing lengths. -/
theorem theta_splitting (theta : ℝ) (ht : 0 < theta) :
    let A := thetaCertificate theta ht
    sourceAlpha A = thetaAlpha theta ∧ A.t = thetaT theta ∧
      (A.a : ℝ) = thetaA theta ∧ A.z = thetaZ theta := by
  dsimp only
  have ha : sourceAlpha (thetaCertificate theta ht) = thetaAlpha theta := by
    unfold sourceAlpha thetaAlpha
    rw [sourceTheta_thetaCertificate, (thetaCertificate_data theta ht).2.2]
  have h := source_splitting_formulas (thetaCertificate theta ht)
  rw [sourceTheta_thetaCertificate, ha] at h
  exact ⟨ha, h.1, h.2.1.trans (congrArg _ h.1), h.2.2.trans (congrArg _ h.1)⟩

/-- Proposition 3.9: the actual constructed copula has exactly G(theta), P(theta). -/
theorem theta_boundary_coefficients (theta : ℝ) (ht : 0 < theta) :
    (thetaCertificate theta ht).copula.giniGamma = thetaG theta ∧
      (thetaCertificate theta ht).copula.spearmanRho = thetaP theta := by
  let A := thetaCertificate theta ht
  have hs := theta_splitting theta ht
  dsimp only at hs
  have hd := thetaCertificate_data theta ht
  dsimp only at hd
  have hm := RhoFootrule.moment_representation A.D
  have hphi : A.D.spearmanFootrule = 1 - 3 * thetaMean theta := by
    rw [hm.2, hd.1]
  have hrho : A.D.spearmanRho = 1 - 6 * thetaSquare theta := by
    rw [hm.1, hd.2.1]
  change A.copula.giniGamma = _ ∧ A.copula.spearmanRho = _
  rw [A.gamma, A.rho, hphi, hrho]
  change 1 - 2 * ((thetaCertificate theta ht).a : ℝ) ^ 2 -
      (thetaCertificate theta ht).z ^ 2 * (1 - (1 - 3 * thetaMean theta)) / 3 = _ ∧
    1 - 2 * ((thetaCertificate theta ht).a : ℝ) ^ 3 -
      (thetaCertificate theta ht).z ^ 3 * (1 - (1 - 6 * thetaSquare theta)) / 4 = _
  rw [hs.2.2.1, hs.2.2.2]
  constructor <;> dsimp [thetaG, thetaP] <;> ring

/-- Theorem 1.1's maximizing statement, for every original theta>0. -/
theorem theta_boundary_maximizes (theta : ℝ) (ht : 0 < theta) (C : Copula 2)
    (hC : C.giniGamma = thetaG theta) : C.spearmanRho ≤ thetaP theta := by
  have h := (thetaCertificate theta ht).supporting_bound C
  rw [(theta_boundary_coefficients theta ht).1, (theta_boundary_coefficients theta ht).2, hC] at h
  linarith

/-- Equation (5), including attainment, in the paper's explicit theta parametrization. -/
theorem theta_boundary_value (theta : ℝ) (ht : 0 < theta) :
    upperRho (thetaG theta) = thetaP theta := by
  have hg : thetaG theta ∈ Set.Icc (-1) 1 :=
    (theta_boundary_coefficients theta ht).1 ▸ (thetaCertificate theta ht).copula.giniGamma_mem_Icc
  obtain ⟨C, hCg, hCr⟩ := upper_boundary_attained hg
  apply le_antisymm
  · rw [← hCr]
    exact theta_boundary_maximizes theta ht C hCg
  · have h := sharp_upper_bound (thetaCertificate theta ht).copula
    rwa [(theta_boundary_coefficients theta ht).1, (theta_boundary_coefficients theta ht).2] at h

/-- Lemma 3.7 stated entirely with the source's explicit functions. -/
theorem theta_parameter_inequalities (theta : ℝ) (ht : 0 < theta) :
    thetaOffset theta < 0 ∧ thetaAlpha theta < 1 ∧
      thetaT theta / 2 ≤ thetaA theta ∧ thetaA theta < thetaT theta := by
  have h := source_parameter_inequalities (thetaCertificate theta ht)
  have hs := theta_splitting theta ht
  dsimp only at hs
  rw [(thetaCertificate_data theta ht).2.2, hs.1, hs.2.1, hs.2.2.1] at h
  exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

end Papers.AnsariRockelSteinmassl2026RhoGamma
