import Verification.Nelsen19

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n20Psi (p t : ℝ) : ℝ := Real.log (t+Real.exp 1)^(-p)
noncomputable def n20PsiDeriv (p t : ℝ) : ℝ := -p*Real.log (t+Real.exp 1)^(-p-1)/(t+Real.exp 1)
noncomputable def n20Second (p t : ℝ) : ℝ :=
  p*Real.log (t+Real.exp 1)^(-p-2)*(Real.log (t+Real.exp 1)+p+1)/(t+Real.exp 1)^2

theorem n20Psi_deriv {p t : ℝ} (ht : 0 ≤ t) : HasDerivAt (n20Psi p) (n20PsiDeriv p t) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hh := (((hasDerivAt_id t).add_const (Real.exp 1)).log hx.ne').rpow_const (p := -p) (Or.inl hl.ne')
  convert hh using 1
  · rfl
  · dsimp [n20PsiDeriv]; ring

theorem n20Psi_deriv2 {p t : ℝ} (ht : 0 ≤ t) : HasDerivAt (n20PsiDeriv p) (n20Second p t) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hd := (hasDerivAt_id t).add_const (Real.exp 1)
  have hh := (((hd.log hx.ne').rpow_const (p := -p-1) (Or.inl hl.ne')).const_mul (-p)).div hd hx.ne'
  have he : Real.log (t+Real.exp 1)^(-p-1) = Real.log (t+Real.exp 1)^(-p-2)*Real.log (t+Real.exp 1) := by
    rw [show -p-1 = (-p-2)+1 by ring, Real.rpow_add_one hl.ne']
  convert hh using 1
  · rfl
  · dsimp [n20Second]
    rw [show -p-1-1 = -p-2 by ring, he]
    field_simp
    ring

theorem n20Psi_convex {p : ℝ} (hp : 0 < p) : ConvexOn ℝ (Ici 0) (n20Psi p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t ht; exact (n20Psi_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n20Psi_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n20Psi_deriv2 (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) (interior_subset ht)
    unfold n20Second
    positivity

theorem n20Psi_antitone {p : ℝ} (hp : 0 < p) : AntitoneOn (n20Psi p) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
  · intro t ht; exact (n20Psi_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n20Psi_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := interior_subset ht
    have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht0
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hp.le) (Real.rpow_nonneg hl.le _))
      (add_nonneg ht0 (Real.exp_pos 1).le)

noncomputable def nelsen20Generator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun := n20Psi θ⁻¹
  invFun u := Real.exp ((u:ℝ)^(-θ))-Real.exp 1
  nonneg t ht := Real.rpow_nonneg (n19_log_pos (by norm_num : (0:ℝ) < 1) ht).le _
  antitone := n20Psi_antitone (inv_pos.mpr hθ)
  convex := n20Psi_convex (inv_pos.mpr hθ)
  inv_nonneg u hu := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    exact sub_nonneg.mpr (Real.exp_le_exp.mpr
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp u.property.2 (neg_nonpos.mpr hθ.le)))
  inv_antitone u v hu huv := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    exact sub_le_sub_right (Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_nonpos hp huv (neg_nonpos.mpr hθ.le))) _
  inv_one := by simp
  right_inv u hu := by
    have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
    dsimp [n20Psi]
    rw [sub_add_cancel, Real.log_exp, ← Real.rpow_mul hp.le]
    simp [hθ.ne']

noncomputable def nelsen20 (θ : ℝ) (hθ : 0 ≤ θ) : Copula 2 :=
  if hz : θ = 0 then independence 2 else
    (nelsen20Generator θ (lt_of_le_of_ne hθ (Ne.symm hz))).copula

theorem nelsen20_zero : nelsen20 0 le_rfl = independence 2 := by simp [nelsen20]

theorem nelsen20_cdf {θ : ℝ} (hθ : 0 < θ) (u v : I) :
    (nelsen20 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.log (Real.exp ((u:ℝ)^(-θ))+Real.exp ((v:ℝ)^(-θ))-Real.exp 1)^(-θ⁻¹) := by
  by_cases hu : u = 0
  · subst u; simp
  by_cases hv : v = 0
  · subst v
    rw [Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)]
    simp
  simp only [nelsen20, hθ.ne', dite_false, BivariateGenerator.cdf_copula,
    BivariateGenerator.cdf, Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ite_false]
  change n20Psi θ⁻¹ ((Real.exp ((u:ℝ)^(-θ))-Real.exp 1)+(Real.exp ((v:ℝ)^(-θ))-Real.exp 1)) = _
  unfold n20Psi
  congr 2
  ring

end Verification
