import Verification.GumbelBarnett

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

noncomputable def n13Psi (p t : ℝ) : ℝ := Real.exp (1-(1+t)^p)
noncomputable def n13PsiDeriv (p t : ℝ) : ℝ := -p*(1+t)^p/(1+t)*n13Psi p t

theorem n13Psi_deriv (p t : ℝ) (ht : 0 < 1+t) :
    HasDerivAt (n13Psi p) (n13PsiDeriv p t) t := by
  have hh := ((((hasDerivAt_id t).const_add 1).rpow_const (p := p) (Or.inl ht.ne')).const_sub 1).exp
  convert hh using 1
  · rfl
  · dsimp [n13PsiDeriv, n13Psi]
    rw [Real.rpow_sub_one ht.ne' p]
    ring

theorem n13Psi_deriv2 (p t : ℝ) (ht : 0 < 1+t) :
    HasDerivAt (n13PsiDeriv p)
      (p*(1+t)^p/(1+t)^2*(p*(1+t)^p-p+1)*n13Psi p t) t := by
  have hb := (hasDerivAt_id t).const_add 1
  have hp := hb.rpow_const (p := p) (Or.inl ht.ne')
  have hh := ((hp.const_mul (-p)).div hb ht.ne').mul (n13Psi_deriv p t ht)
  convert hh using 1
  · rfl
  · dsimp [n13PsiDeriv]
    rw [Real.rpow_sub_one ht.ne' p]
    field_simp
    ring

theorem n13Psi_convex (p : ℝ) (hp : 0 < p) : ConvexOn ℝ (Ici 0) (n13Psi p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t ht
    exact (n13Psi_deriv p t (by linarith [show 0 ≤ t from ht])).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (n13Psi_deriv p t (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (n13Psi_deriv2 p t (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
    have hb : 1 ≤ (1+t)^p := Real.one_le_rpow (by linarith) hp.le
    have hn : 0 ≤ p*(1+t)^p-p+1 := by nlinarith
    exact mul_nonneg (mul_nonneg (by positivity) hn) (Real.exp_pos _).le

theorem n13_inv_base (u : I) : 1 ≤ 1-Real.log (u:ℝ) := by
  have hh := Real.log_nonpos u.property.1 u.property.2
  linarith

private theorem n13_u_pos (u : I) (hu : u ≠ 0) : 0 < (u:ℝ) :=
  lt_of_le_of_ne u.property.1 (Ne.symm (fun h => hu (Subtype.ext h)))

noncomputable def nelsen13Generator (θ : ℝ) (hθ : 0 < θ) : BivariateGenerator where
  toFun := n13Psi θ⁻¹
  invFun u := (1-Real.log (u:ℝ))^θ-1
  nonneg t _ := (Real.exp_pos _).le
  antitone x hx y _ hxy := by
    apply Real.exp_le_exp.mpr
    exact sub_le_sub_left (Real.rpow_le_rpow (by linarith [show 0 ≤ x from hx] : 0 ≤ 1+x)
      (by linarith) (inv_nonneg.mpr hθ.le)) 1
  convex := n13Psi_convex θ⁻¹ (inv_pos.mpr hθ)
  inv_nonneg u _ := sub_nonneg.mpr (Real.one_le_rpow (n13_inv_base u) hθ.le)
  inv_antitone u v hu huv := by
    apply sub_le_sub_right _ 1
    apply Real.rpow_le_rpow (by linarith [n13_inv_base v] : 0 ≤ 1-Real.log (v:ℝ))
    · exact sub_le_sub_left (Real.log_le_log (n13_u_pos u hu) (show (u:ℝ) ≤ v from huv)) 1
    · exact hθ.le
  inv_one := by simp
  right_inv u hu := by
    dsimp [n13Psi]
    rw [add_sub_cancel, Real.rpow_rpow_inv (by linarith [n13_inv_base u]) hθ.ne',
      sub_sub_cancel, Real.exp_log (n13_u_pos u hu)]

noncomputable def nelsen13 (θ : ℝ) (hθ : 0 ≤ θ) : Copula 2 :=
  if hz : θ = 0 then gumbelBarnett 1
  else (nelsen13Generator θ (lt_of_le_of_ne hθ (Ne.symm hz))).copula

theorem nelsen13_zero : nelsen13 0 le_rfl = gumbelBarnett 1 := by simp [nelsen13]

theorem nelsen13_cdf (θ : ℝ) (hθ : 0 < θ) (u v : I) :
    (nelsen13 θ hθ.le).cdf ![u,v] =
      if u = 0 ∨ v = 0 then 0 else
        Real.exp (1-((1-Real.log (u:ℝ))^θ+(1-Real.log (v:ℝ))^θ-1)^θ⁻¹) := by
  by_cases hu : u = 0
  · subst u; simp
  by_cases hv : v = 0
  · subst v
    rw [Copula.cdf_eq_zero_of_coord_eq_zero _ _ 1 (by simp)]
    simp
  simp only [nelsen13, hθ.ne', dite_false, BivariateGenerator.cdf_copula,
    Matrix.cons_val_zero, Matrix.cons_val_one, BivariateGenerator.cdf, hu, hv, or_self, ite_false]
  change n13Psi θ⁻¹ (((1-Real.log (u:ℝ))^θ-1)+((1-Real.log (v:ℝ))^θ-1)) = _
  unfold n13Psi
  congr 3
  ring

theorem nelsen13_one : nelsen13 1 zero_le_one = independence 2 := by
  apply Copula.cdf_injective
  funext x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, nelsen13_cdf 1 zero_lt_one, cdf_independence, Fin.prod_univ_two]
  by_cases hu : x 0 = 0
  · simp [hu]
  by_cases hv : x 1 = 0
  · simp [hv]
  simp only [hu, hv, or_self, ite_false, Real.rpow_one, inv_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  have he : 1-(1-Real.log (x 0:ℝ)+(1-Real.log (x 1:ℝ))-1) = Real.log (x 0:ℝ)+Real.log (x 1:ℝ) := by ring
  rw [he, Real.exp_add, Real.exp_log (n13_u_pos _ hu), Real.exp_log (n13_u_pos _ hv)]

end Verification
