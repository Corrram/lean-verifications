import Verification.Nelsen17Analytic

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n17Ratio (a u : ℝ) : ℝ := ((1+u)^a-1)/n17A a

theorem n17Ratio_pos {a u : ℝ} (ha : a ≠ 0) (hu : 0 < u) : 0 < n17Ratio a u := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · exact div_pos_of_neg_of_neg (sub_neg.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by linarith) hn)) (n17A_neg hn)
  · exact div_pos (sub_pos.mpr (Real.one_lt_rpow (by linarith) hp)) (n17A_pos hp)

theorem n17Ratio_le_one {a u : ℝ} (ha : a ≠ 0) (hu : 0 < u) (hu1 : u ≤ 1) : n17Ratio a u ≤ 1 := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · apply (div_le_one_of_neg (n17A_neg hn)).mpr
    exact sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1+u)
      (by linarith : 1+u ≤ 2) hn.le) 1
  · apply (div_le_one (n17A_pos hp)).mpr
    exact sub_le_sub_right (Real.rpow_le_rpow (by linarith : 0 ≤ 1+u) (by linarith : 1+u ≤ 2) hp.le) 1

theorem n17Ratio_mono {a u v : ℝ} (ha : a ≠ 0) (hu : 0 < u) (huv : u ≤ v) :
    n17Ratio a u ≤ n17Ratio a v := by
  rcases lt_or_gt_of_ne ha with hn | hp
  · exact (div_le_div_right_of_neg (n17A_neg hn)).mpr
      (sub_le_sub_right (Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1+u)
        (by linarith : 1+u ≤ 1+v) hn.le) 1)
  · exact div_le_div_of_nonneg_right
      (sub_le_sub_right (Real.rpow_le_rpow (by linarith : 0 ≤ 1+u)
        (by linarith : 1+u ≤ 1+v) hp.le) 1) (n17A_pos hp).le

noncomputable def n17Generator (a : ℝ) (ha : a ≠ 0) : BivariateGenerator where
  toFun := n17Psi a
  invFun u := -Real.log (n17Ratio a u)
  nonneg _ ht := n17Psi_nonneg ha ht
  antitone := n17Psi_antitone ha
  convex := n17Psi_convex ha
  inv_nonneg u hu := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    exact neg_nonneg.mpr (Real.log_nonpos (n17Ratio_pos ha hp).le (n17Ratio_le_one ha hp u.property.2))
  inv_antitone u v hu huv := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    exact neg_le_neg (Real.log_le_log (n17Ratio_pos ha hp) (n17Ratio_mono ha hp huv))
  inv_one := by
    have he : n17Ratio a 1 = 1 := by
      change ((1+1:ℝ)^a-1)/n17A a = 1
      norm_num only [show (1+1:ℝ) = 2 by norm_num]
      exact div_self (n17A_ne ha)
    change -Real.log (n17Ratio a 1) = 0
    rw [he]; simp
  right_inv u hu := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    have hr := n17Ratio_pos ha hp
    unfold n17Psi n17Base
    rw [neg_neg, Real.exp_log hr]
    have he : 1+n17A a*n17Ratio a u = (1+(u:ℝ))^a := by
      unfold n17Ratio
      field_simp [n17A_ne ha]
      ring
    rw [he, ← Real.rpow_mul (by linarith : 0 ≤ 1+(u:ℝ)), mul_inv_cancel₀ ha, Real.rpow_one]
    ring

noncomputable def nelsen17 (θ : ℝ) (hθ : θ ≠ 0) : Copula 2 :=
  (n17Generator (-θ) (neg_ne_zero.mpr hθ)).copula

theorem nelsen17_cdf (θ : ℝ) (hθ : θ ≠ 0) (u v : I) :
    (nelsen17 θ hθ).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        (1+(((1+(u:ℝ))^(-θ)-1)*((1+(v:ℝ))^(-θ)-1))/((2:ℝ)^(-θ)-1))^(-θ⁻¹)-1 := by
  by_cases hu : u = 0
  · subst u; simp
  by_cases hv : v = 0
  · subst v
    rw [Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)]
    simp
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
  have hv0 : 0 < (v:ℝ) := lt_of_le_of_ne v.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hv))
  have ha := neg_ne_zero.mpr hθ
  simp only [nelsen17, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ite_false]
  change n17Psi (-θ) (-Real.log (n17Ratio (-θ) u)+ -Real.log (n17Ratio (-θ) v)) = _
  unfold n17Psi n17Base
  rw [neg_add, neg_neg, neg_neg, Real.exp_add,
    Real.exp_log (n17Ratio_pos ha hu0), Real.exp_log (n17Ratio_pos ha hv0), inv_neg]
  congr 2
  unfold n17Ratio n17A
  have hn := n17A_ne ha
  dsimp [n17A] at hn
  field_simp

theorem nelsen17_neg_one : nelsen17 (-1) (by norm_num) = independence 2 := by
  apply Copula.ext_cdf_two
  intro u v
  rw [nelsen17_cdf]
  by_cases hu : u = 0
  · subst u; simp
  by_cases hv : v = 0
  · subst v; simp
  norm_num [hu, hv, Real.rpow_one, cdf_independence]

theorem nelsen17_cdf_full (θ : ℝ) (hθ : θ ≠ 0) (u v : I) :
    (nelsen17 θ hθ).cdf ![u,v] =
      (1+(((1+(u:ℝ))^(-θ)-1)*((1+(v:ℝ))^(-θ)-1))/((2:ℝ)^(-θ)-1))^(-θ⁻¹)-1 := by
  rw [nelsen17_cdf]
  by_cases hz : u = 0 ∨ v = 0
  · rcases hz with hu | hv
    · subst u; simp
    · subst v; simp
  · simp only [hz, ite_false]

end Verification
