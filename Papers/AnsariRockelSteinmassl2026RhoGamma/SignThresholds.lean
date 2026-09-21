import Papers.AnsariRockelSteinmassl2026RhoGamma.BoundaryGeometry

/-! # The sharp zero slices and sign thresholds (Corollary 2.4) -/

open ProbabilityTheory Set
open Copula.RankRegion

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

noncomputable def rhoThreshold : ℝ := (144 + 9 * Real.sqrt 6) / 500
noncomputable def gammaThreshold : ℝ := (72 - 3 * Real.sqrt 69) / 169

private noncomputable def zeroGammaS : ℝ := (81 + 26 * Real.sqrt 6) / 60

private theorem zeroGammaS_ge : 1 ≤ zeroGammaS := by
  dsimp [zeroGammaS]
  linarith [Real.sqrt_nonneg 6]

private noncomputable def zeroGammaCertificate : RhoGamma.AuxiliaryCertificate :=
  .halfShift zeroGammaS zeroGammaS_ge

private theorem zeroGamma_lengths :
    zeroGammaCertificate.z = (4 - Real.sqrt 6) / 5 ∧
    (zeroGammaCertificate.a : ℝ) = (1 + Real.sqrt 6) / 5 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have he : zeroGammaS ^ 2 + 2 * (3 / 8 - zeroGammaS / 2) = ((39 + 34 * Real.sqrt 6) / 60) ^ 2 := by
    dsimp [zeroGammaS]
    nlinarith
  have hr : Real.sqrt (zeroGammaS ^ 2 + 2 * (3 / 8 - zeroGammaS / 2)) = (39 + 34 * Real.sqrt 6) / 60 := by
    rw [he, Real.sqrt_sq (by positivity)]
  have hz : zeroGammaCertificate.z = (4 - Real.sqrt 6) / 5 := by
    change 1 / (1 + (zeroGammaS + Real.sqrt (zeroGammaS ^ 2 + 2 * (3 / 8 - zeroGammaS / 2))) / 2) = _
    rw [hr]
    dsimp [zeroGammaS]
    field_simp
    nlinarith
  refine ⟨hz, ?_⟩
  have ha := zeroGammaCertificate.a_add_z
  rw [hz] at ha
  linarith

private theorem zeroGamma_coefficients :
    zeroGammaCertificate.copula.giniGamma = 0 ∧
    zeroGammaCertificate.copula.spearmanRho = rhoThreshold := by
  have hg := zeroGammaCertificate.gamma
  have hr := zeroGammaCertificate.rho
  have hD : zeroGammaCertificate.D = RhoFootrule.halfTurn := rfl
  rw [hD, RhoFootrule.halfTurn_footrule, zeroGamma_lengths.1, zeroGamma_lengths.2] at hg
  rw [hD, RhoFootrule.halfTurn_rho, zeroGamma_lengths.1, zeroGamma_lengths.2] at hr
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
  have hs3 : Real.sqrt 6 ^ 3 = 6 * Real.sqrt 6 := by rw [pow_succ, hs]
  constructor
  · rw [hg]
    nlinarith only [hs]
  · rw [hr]
    unfold rhoThreshold
    ring_nf
    simp only [hs, hs3]
    ring

private noncomputable def zeroRhoS : ℝ := (276 + 31 * Real.sqrt 69) / 132

private theorem zeroRhoS_ge : 1 ≤ zeroRhoS := by
  dsimp [zeroRhoS]
  linarith [Real.sqrt_nonneg 69]

private noncomputable def zeroRhoCertificate : RhoGamma.AuxiliaryCertificate :=
  .halfShift zeroRhoS zeroRhoS_ge

private theorem zeroRho_lengths :
    zeroRhoCertificate.z = (11 - Real.sqrt 69) / 13 ∧
    (zeroRhoCertificate.a : ℝ) = (2 + Real.sqrt 69) / 13 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 69 by norm_num)
  have he : zeroRhoS ^ 2 + 2 * (3 / 8 - zeroRhoS / 2) = ((186 + 35 * Real.sqrt 69) / 132) ^ 2 := by
    dsimp [zeroRhoS]
    nlinarith
  have hr : Real.sqrt (zeroRhoS ^ 2 + 2 * (3 / 8 - zeroRhoS / 2)) = (186 + 35 * Real.sqrt 69) / 132 := by
    rw [he, Real.sqrt_sq (by positivity)]
  have hz : zeroRhoCertificate.z = (11 - Real.sqrt 69) / 13 := by
    change 1 / (1 + (zeroRhoS + Real.sqrt (zeroRhoS ^ 2 + 2 * (3 / 8 - zeroRhoS / 2))) / 2) = _
    rw [hr]
    dsimp [zeroRhoS]
    field_simp
    nlinarith
  refine ⟨hz, ?_⟩
  have ha := zeroRhoCertificate.a_add_z
  rw [hz] at ha
  linarith

private theorem zeroRho_coefficients :
    zeroRhoCertificate.copula.giniGamma = -gammaThreshold ∧
    zeroRhoCertificate.copula.spearmanRho = 0 := by
  have hg := zeroRhoCertificate.gamma
  have hr := zeroRhoCertificate.rho
  have hD : zeroRhoCertificate.D = RhoFootrule.halfTurn := rfl
  rw [hD, RhoFootrule.halfTurn_footrule, zeroRho_lengths.1, zeroRho_lengths.2] at hg
  rw [hD, RhoFootrule.halfTurn_rho, zeroRho_lengths.1, zeroRho_lengths.2] at hr
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 69 by norm_num)
  have hs3 : Real.sqrt 69 ^ 3 = 69 * Real.sqrt 69 := by rw [pow_succ, hs]
  constructor
  · rw [hg]
    unfold gammaThreshold
    nlinarith only [hs]
  · rw [hr]
    ring_nf
    simp only [hs, hs3]
    ring

theorem upperRho_zero : upperRho 0 = rhoThreshold := by
  have h := upperRho_parameter (.halfShift zeroGammaS zeroGammaS_ge)
  have hg : (RhoGamma.UpperParameter.halfShift zeroGammaS zeroGammaS_ge).gamma = 0 :=
    (RhoGamma.UpperParameter.gamma_coefficient _).symm.trans zeroGamma_coefficients.1
  have hr : (RhoGamma.UpperParameter.halfShift zeroGammaS zeroGammaS_ge).rho = rhoThreshold :=
    (RhoGamma.UpperParameter.rho_coefficient _).symm.trans zeroGamma_coefficients.2
  rwa [hg, hr] at h

theorem upperRho_neg_gammaThreshold : upperRho (-gammaThreshold) = 0 := by
  have h := upperRho_parameter (.halfShift zeroRhoS zeroRhoS_ge)
  have hg : (RhoGamma.UpperParameter.halfShift zeroRhoS zeroRhoS_ge).gamma = -gammaThreshold :=
    (RhoGamma.UpperParameter.gamma_coefficient _).symm.trans zeroRho_coefficients.1
  have hr : (RhoGamma.UpperParameter.halfShift zeroRhoS zeroRhoS_ge).rho = 0 :=
    (RhoGamma.UpperParameter.rho_coefficient _).symm.trans zeroRho_coefficients.2
  rwa [hg, hr] at h

theorem gammaThreshold_mem : gammaThreshold ∈ Icc (0 : ℝ) 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 69 by norm_num)
  have hn := Real.sqrt_nonneg 69
  dsimp [gammaThreshold]
  constructor <;> nlinarith

/-- Exactly the attainable rho values at gamma zero, including both endpoints. -/
theorem zero_gamma_slice (r : ℝ) : (r, 0) ∈ region ↔ |r| ≤ rhoThreshold := by
  rw [exact_region, neg_zero, upperRho_zero, abs_le]
  norm_num

/-- Exactly the attainable gamma values at rho zero, including both endpoints. -/
theorem zero_rho_slice (g : ℝ) : (0, g) ∈ region ↔ |g| ≤ gammaThreshold := by
  have ht : -gammaThreshold ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [gammaThreshold_mem.1, gammaThreshold_mem.2]
  have hsign (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      0 ≤ upperRho x ↔ -gammaThreshold ≤ x := by
    rw [← upperRho_neg_gammaThreshold]
    exact upperRho_strictMono.le_iff_le ht hx
  rw [exact_region, abs_le]
  constructor
  · rintro ⟨hg, hl, hu⟩
    have hn : -g ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hg.1, hg.2]
    exact ⟨(hsign g hg).mp hu, by linarith [(hsign (-g) hn).mp (by linarith)]⟩
  · rintro ⟨hl, hu⟩
    have hg : g ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [gammaThreshold_mem.2]
    have hn : -g ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hg.1, hg.2]
    exact ⟨hg, by linarith [(hsign (-g) hn).mpr (by linarith)], (hsign g hg).mpr hl⟩

private theorem gamma_pos_of_rho_gt (C : Copula 2) (hr : rhoThreshold < C.spearmanRho) :
    0 < C.giniGamma := by
  by_contra h
  have hh := upperRho_strictMono.monotoneOn C.giniGamma_mem_Icc
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) (le_of_not_gt h)
  rw [upperRho_zero] at hh
  linarith [sharp_upper_bound C]

private theorem rho_pos_of_gamma_gt (C : Copula 2) (hg : gammaThreshold < C.giniGamma) :
    0 < C.spearmanRho := by
  have ht : -gammaThreshold ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [gammaThreshold_mem.1, gammaThreshold_mem.2]
  have hn : -C.giniGamma ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [C.giniGamma_mem_Icc.1, C.giniGamma_mem_Icc.2]
  have hh := upperRho_strictMono hn ht (by linarith : -C.giniGamma < -gammaThreshold)
  rw [upperRho_neg_gammaThreshold] at hh
  linarith [sharp_lower_bound C]

/-- Above the sharp absolute rho threshold the coefficients have the same strict sign. -/
theorem same_sign_of_abs_rho_gt (C : Copula 2) (h : rhoThreshold < |C.spearmanRho|) :
    0 < C.spearmanRho * C.giniGamma := by
  have ht : 0 < rhoThreshold := by unfold rhoThreshold; positivity
  by_cases hr : 0 ≤ C.spearmanRho
  · rw [abs_of_nonneg hr] at h
    exact mul_pos (ht.trans h) (gamma_pos_of_rho_gt C h)
  · rw [abs_of_neg (lt_of_not_ge hr)] at h
    have hh := gamma_pos_of_rho_gt (C.reflect {1}) (by rwa [Copula.spearmanRho_reflect_second])
    rw [Copula.giniGamma_reflect_second] at hh
    exact mul_pos_of_neg_of_neg (lt_of_not_ge hr) (by linarith)

/-- Above the sharp absolute gamma threshold the coefficients have the same strict sign. -/
theorem same_sign_of_abs_gamma_gt (C : Copula 2) (h : gammaThreshold < |C.giniGamma|) :
    0 < C.spearmanRho * C.giniGamma := by
  by_cases hg : 0 ≤ C.giniGamma
  · rw [abs_of_nonneg hg] at h
    exact mul_pos (rho_pos_of_gamma_gt C h) (lt_of_le_of_lt gammaThreshold_mem.1 h)
  · rw [abs_of_neg (lt_of_not_ge hg)] at h
    have hh := rho_pos_of_gamma_gt (C.reflect {1}) (by rwa [Copula.giniGamma_reflect_second])
    rw [Copula.spearmanRho_reflect_second] at hh
    exact mul_pos_of_neg_of_neg (by linarith) (lt_of_not_ge hg)

end Papers.AnsariRockelSteinmassl2026RhoGamma
