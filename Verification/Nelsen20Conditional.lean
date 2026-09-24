import Verification.Nelsen20

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n20LogDeriv (p t : ℝ) : ℝ :=
  -Real.log (t+Real.exp 1)-(p+1)*Real.log (Real.log (t+Real.exp 1))
noncomputable def n20LogDerivPrime (p t : ℝ) : ℝ :=
  -1/(t+Real.exp 1)-(p+1)/((t+Real.exp 1)*Real.log (t+Real.exp 1))

theorem n20LogDeriv_deriv {p t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (n20LogDeriv p) (n20LogDerivPrime p t) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hd := ((hasDerivAt_id t).add_const (Real.exp 1)).log hx.ne'
  have hh := hd.neg.sub ((hd.log hl.ne').const_mul (p+1))
  convert hh using 1
  · rfl
  · dsimp [n20LogDerivPrime]; field_simp

theorem n20LogDeriv_deriv2 {p t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (n20LogDerivPrime p)
      (1/(t+Real.exp 1)^2+(p+1)*(Real.log (t+Real.exp 1)+1)/
        ((t+Real.exp 1)*Real.log (t+Real.exp 1))^2) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hd := (hasDerivAt_id t).add_const (Real.exp 1)
  have hlog := hd.log hx.ne'
  have hh := ((hasDerivAt_const t (-1)).div hd hx.ne').sub
    ((hasDerivAt_const t (p+1)).div (hd.mul hlog) (mul_ne_zero hx.ne' hl.ne'))
  convert hh using 1
  · rfl
  · dsimp; field_simp; ring

theorem n20PsiDeriv_logconvex {p : ℝ} (hp : 0 < p) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-n20PsiDeriv p t)) := by
  have hc : ConvexOn ℝ (Ioi 0) (n20LogDeriv p) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (n20LogDeriv_deriv ht.le).continuousAt.continuousWithinAt
    · intro t ht; exact (n20LogDeriv_deriv (interior_subset ht).le).hasDerivWithinAt
    · intro t ht; exact (n20LogDeriv_deriv2 (interior_subset ht).le).hasDerivWithinAt
    · intro t ht
      have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) (le_of_lt (interior_subset ht))
      positivity
  apply (hc.add_const (Real.log p)).congr
  intro t ht
  have hx : 0 < t+Real.exp 1 := add_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht.le
  have he : -n20PsiDeriv p t = p*Real.log (t+Real.exp 1)^(-p-1)/(t+Real.exp 1) := by
    dsimp [n20PsiDeriv]; ring
  simp only [he, Real.log_div (mul_ne_zero hp.ne' (Real.rpow_pos_of_pos hl _).ne') hx.ne',
    Real.log_mul hp.ne' (Real.rpow_pos_of_pos hl _).ne', Real.log_rpow hl,
    Pi.add_apply, n20LogDeriv]
  ring

theorem nelsen20_isCI (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen20 θ hθ).IsCI := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen20_zero]
    exact isCI_independence
  have hp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
  let φ : ℝ → ℝ := fun u => Real.exp (u^(-θ))-Real.exp 1
  let φ' : ℝ → ℝ := fun u => Real.exp (u^(-θ))*(-θ*u^(-θ-1))
  have hh : (nelsen20Generator θ hp).copula.IsCI := by
    apply generator_isCI_of_logconvex_neg_deriv (nelsen20Generator θ hp) φ φ' (n20PsiDeriv θ⁻¹)
    · intro u _ _; rfl
    · intro u hu
      apply sub_pos.mpr (Real.exp_lt_exp.mpr _)
      exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hu.1 hu.2 (neg_neg_of_pos hp)
    · intro u hu
      have hd := (((hasDerivAt_id u).rpow_const (p := -θ) (Or.inl hu.1.ne')).exp).sub_const (Real.exp 1)
      convert hd using 1
      · rfl
      · dsimp [φ']; ring
    · intro t ht; exact n20Psi_deriv ht.le
    · intro t ht
      have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht.le
      exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos (inv_pos.mpr hp))
        (Real.rpow_pos_of_pos hl _)) (add_pos ht (Real.exp_pos 1))
    · exact n20PsiDeriv_logconvex (inv_pos.mpr hp)
  simpa only [nelsen20, hz, dite_false] using hh

end Verification
