import Papers.OrendayLaresRockel2026XiBeta.SIBoundFinal
import Papers.OrendayLaresRockel2026XiBeta.Section2Classes
import Copula.Symmetry
import Copula.Rank.Integration

/-! # Elementary properties of the two-branch copulas `R_b` (Proposition 5.3 (i))

Explicit distribution function of `R_b`, the identification `R_1 = M`, radial symmetry,
failure of exchangeability for `b < 1`, and failure of stochastic increasingness of `R_bᵀ`
for `b < 1` (via the concavity criterion).
-/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Papers.OrendayLaresRockel2026XiBeta

/-- The median section `A_b(u) = min {u, (2u + b)/4, 1/2}` of equation (5.5). -/
noncomputable def rbA (b u : ℝ) : ℝ := min (min u ((2 * u + b) / 4)) (1 / 2)

/-- Distribution function of `R_b`, lower half `v ≤ 1/2`. -/
theorem Rb_cdf_of_le_half {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (u v : I) (hv : (v : ℝ) ≤ 1 / 2) :
    (Rb b hb).cdf ![u, v] = min (rbA b u) v := by
  rw [Rb, MedianSection.cdf_completion_of_le_half _ _ _ hv, rightSection_A hb u.2.1]
  rfl

/-- Distribution function of `R_b`, upper half `v ≥ 1/2`. -/
theorem Rb_cdf_of_half_le {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (u v : I) (hv : 1 / 2 ≤ (v : ℝ)) :
    (Rb b hb).cdf ![u, v] = min (u : ℝ) (rbA b u + v - 1 / 2) := by
  rw [Rb, MedianSection.cdf_completion_of_half_le _ _ _ hv, rightSection_A hb u.2.1]
  rfl

theorem rbA_symm {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    rbA b (1 - u) = rbA b u - u + 1 / 2 := by
  obtain ⟨hb0, hb1⟩ := hb
  obtain ⟨hu0, hu1⟩ := hu
  unfold rbA
  simp only [min_def]
  split_ifs <;> linarith

/-- **Proposition 5.3 (i)**: `R_b` is radially symmetric. -/
theorem Rb_isRadiallySymmetric {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) :
    (Rb b hb).IsRadiallySymmetric := by
  rw [Copula.isRadiallySymmetric_iff]
  intro u v
  have hs := rbA_symm hb u.2
  rcases le_total (v : ℝ) (1 / 2) with h | h
  · rw [Rb_cdf_of_le_half hb u v h,
      Rb_cdf_of_half_le hb (unitInterval.symm u) (unitInterval.symm v)
        (by simp only [unitInterval.coe_symm_eq]; linarith)]
    simp only [unitInterval.coe_symm_eq]
    rw [hs]
    simp only [min_def]
    split_ifs <;> linarith
  · rw [Rb_cdf_of_half_le hb u v h,
      Rb_cdf_of_le_half hb (unitInterval.symm u) (unitInterval.symm v)
        (by simp only [unitInterval.coe_symm_eq]; linarith)]
    simp only [unitInterval.coe_symm_eq]
    rw [hs]
    simp only [min_def]
    split_ifs <;> linarith

/-- **Proposition 5.3 (i)**: `R_1 = M`. -/
theorem Rb_one_eq_comonotonic (hb : (1 : ℝ) ∈ Icc (0 : ℝ) 1) :
    Rb 1 hb = Copula.comonotonic 2 := by
  apply Copula.ext_cdf_two
  intro u v
  rw [Copula.cdf_comonotonic_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hu := u.2
  have hv := v.2
  rcases le_total (v : ℝ) (1 / 2) with h | h
  · rw [Rb_cdf_of_le_half hb u v h]
    unfold rbA
    simp only [min_def]
    split_ifs <;> linarith [hu.1, hu.2, hv.1, hv.2]
  · rw [Rb_cdf_of_half_le hb u v h]
    unfold rbA
    simp only [min_def]
    split_ifs <;> linarith [hu.1, hu.2, hv.1, hv.2]

/-- The point `v₀ = (1 + b)/4 = A_b(1/2)` of the unit interval. -/
noncomputable def rbV0 (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) : I :=
  ⟨(1 + b) / 4, by linarith [hb.1], by linarith [hb.2]⟩

theorem rbV0_le_half (b : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) : ((rbV0 b hb : I) : ℝ) ≤ 1 / 2 := by
  change (1 + b) / 4 ≤ 1 / 2
  linarith [hb.2]

theorem rbA_half {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) : rbA b (1 / 2) = (1 + b) / 4 := by
  unfold rbA
  simp only [min_def]
  split_ifs <;> linarith [hb.1, hb.2]

/-- **Proposition 5.3 (i)**: for `b < 1`, `R_b` is not exchangeable:
`R_b(1/2, v₀) = v₀ > (1 + 3b)/8 = R_b(v₀, 1/2)` where `v₀ = (1 + b)/4`. -/
theorem Rb_not_exchangeable {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hb1 : b < 1) :
    ¬ (Rb b hb).IsExchangeable := by
  intro h
  have h1 := (Copula.isExchangeable_iff _).1 h Copula.unitHalf (rbV0 b hb)
  have hh : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
  have e1 : (Rb b hb).cdf ![Copula.unitHalf, rbV0 b hb] = (1 + b) / 4 := by
    rw [Rb_cdf_of_le_half hb _ _ (rbV0_le_half b hb), hh, rbA_half hb]
    exact min_eq_left (le_refl _)
  have e2 : (Rb b hb).cdf ![rbV0 b hb, Copula.unitHalf] = (1 + 3 * b) / 8 := by
    rw [Rb_cdf_of_le_half hb _ _ (by rw [hh]), hh]
    change min (rbA b ((1 + b) / 4)) (1 / 2) = _
    unfold rbA
    simp only [min_def]
    split_ifs <;> linarith [hb.1, hb.2]
  rw [e1, e2] at h1
  linarith

/-- **Proposition 5.3 (i)**: for `b < 1`, `R_bᵀ` is not SI, because `v ↦ R_b(1/2, v)` is not
concave (concavity criterion `transpose_isSI_iff_concave`). -/
theorem Rb_transpose_not_isSI {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (hb1 : b < 1) :
    ¬ (Rb b hb).transpose.IsSI := by
  intro h
  rw [transpose_isSI_iff_concave] at h
  have hh : ((Copula.unitHalf : I) : ℝ) = 1 / 2 := rfl
  let c : I := ⟨(3 - b) / 4, by linarith [hb.2], by linarith [hb.1]⟩
  have h1 := h (rbV0 b hb) Copula.unitHalf c Copula.unitHalf
    (by change (1 + b) / 4 ≤ 1 / 2; linarith) (by change 1 / 2 ≤ (3 - b) / 4; linarith)
  have ea : (Rb b hb).cdf ![Copula.unitHalf, rbV0 b hb] = (1 + b) / 4 := by
    rw [Rb_cdf_of_le_half hb _ _ (rbV0_le_half b hb), hh, rbA_half hb]
    exact min_eq_left (le_refl _)
  have eb : (Rb b hb).cdf ![Copula.unitHalf, Copula.unitHalf] = (1 + b) / 4 := by
    rw [Rb_cdf_of_le_half hb _ _ (by rw [hh]), hh, rbA_half hb]
    exact min_eq_left (by linarith)
  have ec : (Rb b hb).cdf ![Copula.unitHalf, c] = 1 / 2 := by
    rw [Rb_cdf_of_half_le hb _ _ (by change 1 / 2 ≤ (3 - b) / 4; linarith), hh, rbA_half hb]
    change min (1 / 2 : ℝ) ((1 + b) / 4 + (3 - b) / 4 - 1 / 2) = _
    rw [min_eq_left (by linarith)]
  rw [ea, eb, ec] at h1
  change ((1 / 2 : ℝ) - (1 + b) / 4) * (1 / 2) + ((3 - b) / 4 - 1 / 2) * ((1 + b) / 4) ≤
    ((3 - b) / 4 - (1 + b) / 4) * ((1 + b) / 4) at h1
  nlinarith

end Papers.OrendayLaresRockel2026XiBeta
