import Verification.BB1Conditional
import Copula.Families.Clayton

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n19Psi (θ t : ℝ) : ℝ := θ / Real.log (t+Real.exp θ)
noncomputable def n19PsiDeriv (θ t : ℝ) : ℝ :=
  -θ / ((t+Real.exp θ)*Real.log (t+Real.exp θ)^2)

theorem n19_log_pos {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    0 < Real.log (t+Real.exp θ) := by
  apply Real.log_pos
  have he : 1 < Real.exp θ := Real.one_lt_exp_iff.mpr hθ
  linarith

theorem n19Psi_deriv {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    HasDerivAt (n19Psi θ) (n19PsiDeriv θ t) t := by
  have hp : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hl := ((hasDerivAt_id t).add_const (Real.exp θ)).log hp.ne'
  have hh := (hasDerivAt_const t θ).div hl (n19_log_pos hθ ht).ne'
  convert hh using 1
  · rfl
  · dsimp [n19PsiDeriv]; field_simp; ring

theorem n19Psi_deriv2 {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    HasDerivAt (n19PsiDeriv θ)
      (θ*(Real.log (t+Real.exp θ)+2)/((t+Real.exp θ)^2*Real.log (t+Real.exp θ)^3)) t := by
  have hp : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hlp := n19_log_pos hθ ht
  have hx := (hasDerivAt_id t).add_const (Real.exp θ)
  have hl := hx.log hp.ne'
  have hh := (hasDerivAt_const t (-θ)).div (hx.mul (hl.pow 2)) (mul_ne_zero hp.ne' (pow_ne_zero _ hlp.ne'))
  convert hh using 1
  · rfl
  · dsimp; field_simp; ring

theorem n19Psi_antitone {θ : ℝ} (hθ : 0 < θ) : AntitoneOn (n19Psi θ) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro t ht; exact (n19Psi_deriv hθ ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n19Psi_deriv hθ (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ.le)
      (mul_nonneg (add_nonneg (interior_subset ht) (Real.exp_pos θ).le) (sq_nonneg _))

theorem n19Psi_convex {θ : ℝ} (hθ : 0 < θ) : ConvexOn ℝ (Ici 0) (n19Psi θ) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t ht; exact (n19Psi_deriv hθ ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n19Psi_deriv hθ (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n19Psi_deriv2 hθ (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact div_nonneg (mul_nonneg hθ.le (by linarith [n19_log_pos hθ (interior_subset ht)]))
      (mul_nonneg (sq_nonneg _) (pow_nonneg (n19_log_pos hθ (interior_subset ht)).le _))

noncomputable def nelsen19Generator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun := n19Psi θ
  invFun u := Real.exp (θ/(u:ℝ))-Real.exp θ
  nonneg t ht := div_nonneg hθ.le (n19_log_pos hθ ht).le
  antitone := n19Psi_antitone hθ
  convex := n19Psi_convex hθ
  inv_nonneg u hu := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    apply sub_nonneg.mpr (Real.exp_le_exp.mpr _)
    exact (le_div_iff₀ hp).mpr (mul_le_of_le_one_right hθ.le u.property.2)
  inv_antitone u v hu huv := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    exact sub_le_sub_right (Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hθ.le hp huv)) _
  inv_one := by simp
  right_inv u hu := by
    have hp : (u:ℝ) ≠ 0 := unitInterval.coe_ne_zero.mpr hu
    dsimp [n19Psi]
    rw [sub_add_cancel, Real.log_exp]
    field_simp

noncomputable def nelsen19 (θ : ℝ) (hθ : 0 ≤ θ) : Copula 2 :=
  if hz : θ = 0 then clayton 2 1 (by norm_num) else
    (nelsen19Generator θ (lt_of_le_of_ne hθ (Ne.symm hz))).copula

theorem nelsen19_zero : nelsen19 0 le_rfl = clayton 2 1 (by norm_num) := by
  simp [nelsen19]

theorem nelsen19_cdf {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (nelsen19 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        θ/Real.log (Real.exp (θ/(u:ℝ))+Real.exp (θ/(v:ℝ))-Real.exp θ) := by
  by_cases hu : u = 0
  · subst u; simp
  by_cases hv : v = 0
  · subst v
    rw [Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)]
    simp
  simp only [nelsen19, hθ.ne', dite_false, BivariateGenerator.cdf_copula,
    BivariateGenerator.cdf, Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ite_false]
  change n19Psi θ ((Real.exp (θ/(u:ℝ))-Real.exp θ)+(Real.exp (θ/(v:ℝ))-Real.exp θ)) = _
  unfold n19Psi
  congr 2
  ring

end Verification
