import Verification.Nelsen19
import Verification.ArchimedeanCI
import Copula.Dependence.Clayton

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n19LogDeriv (θ t : ℝ) : ℝ :=
  -Real.log (t+Real.exp θ)-2*Real.log (Real.log (t+Real.exp θ))
noncomputable def n19LogDerivPrime (θ t : ℝ) : ℝ :=
  -1/(t+Real.exp θ)-2/((t+Real.exp θ)*Real.log (t+Real.exp θ))

theorem n19LogDeriv_deriv {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    HasDerivAt (n19LogDeriv θ) (n19LogDerivPrime θ t) t := by
  have hp : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hlp := n19_log_pos hθ ht
  have hl := ((hasDerivAt_id t).add_const (Real.exp θ)).log hp.ne'
  have hh := hl.neg.sub ((hl.log hlp.ne').const_mul 2)
  convert hh using 1
  · rfl
  · dsimp [n19LogDerivPrime]; field_simp

theorem n19LogDeriv_deriv2 {θ t : ℝ} (hθ : 0 < θ) (ht : 0 ≤ t) :
    HasDerivAt (n19LogDerivPrime θ)
      (1/(t+Real.exp θ)^2+2*(Real.log (t+Real.exp θ)+1)/
        ((t+Real.exp θ)*Real.log (t+Real.exp θ))^2) t := by
  have hp : 0 < t+Real.exp θ := add_pos_of_nonneg_of_pos ht (Real.exp_pos θ)
  have hlp := n19_log_pos hθ ht
  have hx := (hasDerivAt_id t).add_const (Real.exp θ)
  have hl := hx.log hp.ne'
  have hh := ((hasDerivAt_const t (-1)).div hx hp.ne').sub
    ((hasDerivAt_const t 2).div (hx.mul hl) (mul_ne_zero hp.ne' hlp.ne'))
  convert hh using 1
  · rfl
  · dsimp; field_simp; ring

theorem n19PsiDeriv_logconvex {θ : ℝ} (hθ : 0 < θ) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-n19PsiDeriv θ t)) := by
  have hc : ConvexOn ℝ (Ioi 0) (n19LogDeriv θ) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (n19LogDeriv_deriv hθ ht.le).continuousAt.continuousWithinAt
    · intro t ht; exact (n19LogDeriv_deriv hθ (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact (n19LogDeriv_deriv2 hθ (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      apply add_nonneg (by positivity)
      apply div_nonneg _ (sq_nonneg _)
      have hl := n19_log_pos hθ (le_of_lt (interior_subset ht))
      positivity
  apply (hc.add_const (Real.log θ)).congr
  intro t ht
  have hp : 0 < t+Real.exp θ := add_pos ht (Real.exp_pos θ)
  have hlp := n19_log_pos hθ ht.le
  simp only [n19PsiDeriv, neg_div, neg_neg,
    Real.log_div hθ.ne' (mul_ne_zero hp.ne' (pow_ne_zero _ hlp.ne')),
    Real.log_mul hp.ne' (pow_ne_zero 2 hlp.ne'), Real.log_pow, Pi.add_apply, n19LogDeriv]
  ring

theorem nelsen19_isCI (θ : ℝ) (hθ : 0 ≤ θ) : (nelsen19 θ hθ).IsCI := by
  by_cases hz : θ = 0
  · subst θ
    rw [nelsen19_zero]
    exact isCI_clayton_positive 1 (by norm_num)
  have hp : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hz)
  let φ : ℝ → ℝ := fun u => Real.exp (θ/u)-Real.exp θ
  let φ' : ℝ → ℝ := fun u => Real.exp (θ/u)*(-θ/u^2)
  have hh : (nelsen19Generator θ hp).copula.IsCI := by
    apply generator_isCI_of_logconvex_neg_deriv (nelsen19Generator θ hp) φ φ' (n19PsiDeriv θ)
    · intro u _ _; rfl
    · intro u hu
      apply sub_pos.mpr (Real.exp_lt_exp.mpr _)
      exact (lt_div_iff₀ hu.1).mpr (mul_lt_of_lt_one_right hp hu.2)
    · intro u hu
      have hd := (((hasDerivAt_const u θ).div (hasDerivAt_id u) hu.1.ne').exp).sub_const (Real.exp θ)
      convert hd using 1
      · rfl
      · dsimp [φ']; ring
    · intro t ht; exact n19Psi_deriv hp ht.le
    · intro t ht
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hp)
        (mul_pos (add_pos ht (Real.exp_pos θ)) (sq_pos_of_pos (n19_log_pos hp ht.le)))
    · exact n19PsiDeriv_logconvex hp
  simpa only [nelsen19, hz, dite_false] using hh

end Verification
