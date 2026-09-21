import Papers.AnsariRockelSteinmassl2026RhoGamma.ExactRegion

/-! # The normalized splitting parameters in equations (18) and Lemma 3.7 -/

open ProbabilityTheory Copula.RankRegion
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

/-- The source parameter is the reciprocal auxiliary multiplier. -/
noncomputable def sourceTheta (A : RhoGamma.AuxiliaryCertificate) : ℝ := 1 / A.s

/-- The source normalizes the central length by the supporting multiplier. -/
noncomputable def sourceAlpha (A : RhoGamma.AuxiliaryCertificate) : ℝ :=
  (1 + Real.sqrt (1 + 2 * (sourceTheta A) ^ 2 * A.c)) / 2

private theorem alpha_eq_ratio (A : RhoGamma.AuxiliaryCertificate) :
    sourceAlpha A = RhoGamma.splitRatio A.s A.c / A.s := by
  have hs := A.s_pos
  have hsn := ne_of_gt hs
  have hd : 0 ≤ A.s ^ 2 + 2 * A.c := (sq_nonneg A.w).trans A.discriminant
  have he : 1 + 2 * (sourceTheta A) ^ 2 * A.c =
      (A.s ^ 2 + 2 * A.c) / A.s ^ 2 := by
    dsimp [sourceTheta]
    field_simp
  unfold sourceAlpha
  rw [he, Real.sqrt_div hd, Real.sqrt_sq hs.le]
  unfold RhoGamma.splitRatio
  field_simp

/-- Equation (18), with the same theta and alpha normalizations as the paper. -/
theorem source_splitting_formulas (A : RhoGamma.AuxiliaryCertificate) :
    A.t = 1 / (sourceTheta A + sourceAlpha A) ∧
      (A.a : ℝ) = sourceAlpha A * A.t ∧ A.z = sourceTheta A * A.t := by
  have hs := ne_of_gt A.s_pos
  rw [alpha_eq_ratio]
  dsimp [sourceTheta, RhoGamma.AuxiliaryCertificate.t, RhoGamma.AuxiliaryCertificate.a,
    RhoGamma.AuxiliaryCertificate.z, RhoGamma.supportingSlope,
    RhoGamma.centralLength, RhoGamma.cornerLength]
  constructor
  · field_simp
  constructor <;> field_simp

/-- All inequalities in Lemma 3.7, for every constructed branch certificate. -/
theorem source_parameter_inequalities (A : RhoGamma.AuxiliaryCertificate) :
    A.c < 0 ∧ (sourceTheta A) ^ 2 * A.w ^ 2 ≤ 1 + 2 * (sourceTheta A) ^ 2 * A.c ∧
      (1 + sourceTheta A * A.w) / 2 ≤ sourceAlpha A ∧ sourceAlpha A < 1 ∧
      A.t / 2 ≤ (A.a : ℝ) ∧ (A.a : ℝ) < A.t := by
  obtain ⟨_, hlt, hlow, _⟩ := RhoGamma.splitRatio_properties A.s_pos A.c_neg A.w_nonneg A.discriminant
  have hs := A.s_pos
  have hsq : 0 < A.s ^ 2 := sq_pos_of_pos hs
  have hdisc : (sourceTheta A) ^ 2 * A.w ^ 2 ≤ 1 + 2 * (sourceTheta A) ^ 2 * A.c := by
    dsimp [sourceTheta]
    apply (mul_le_mul_iff_left₀ hsq).mp
    convert A.discriminant using 1 <;> field_simp
  have halow : (1 + sourceTheta A * A.w) / 2 ≤ sourceAlpha A := by
    rw [alpha_eq_ratio]
    dsimp [sourceTheta]
    apply (mul_le_mul_iff_left₀ hs).mp
    convert (show (A.s + A.w) / 2 ≤ RhoGamma.splitRatio A.s A.c by linarith) using 1 <;> field_simp
  have halt : sourceAlpha A < 1 := by
    rw [alpha_eq_ratio]
    exact (div_lt_one hs).mpr hlt
  have hhalf : A.t / 2 ≤ (A.a : ℝ) := by
    have hh := A.slope_bound
    have hp := mul_nonneg A.z_pos.le A.w_nonneg
    linarith
  exact ⟨A.c_neg, hdisc, halow, halt, hhalf, A.a_lt_t⟩

/-- The potential matching equation directly in the source normalization. -/
theorem source_alpha_matching (A : RhoGamma.AuxiliaryCertificate) :
    (sourceAlpha A) ^ 2 - sourceAlpha A = (sourceTheta A) ^ 2 * A.c / 2 := by
  have he := (RhoGamma.splitRatio_properties A.s_pos A.c_neg A.w_nonneg A.discriminant).2.2.2
  rw [alpha_eq_ratio]
  dsimp [sourceTheta]
  field_simp [ne_of_gt A.s_pos]
  nlinarith only [he]

end Papers.AnsariRockelSteinmassl2026RhoGamma
