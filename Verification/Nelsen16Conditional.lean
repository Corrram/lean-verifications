import Verification.Nelsen16Order
import Verification.ArchimedeanCI
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem n16Psi_pos {θ t : ℝ} (hθ : 0 < θ) : 0 < n16Psi θ t := by
  have he := n16Rad_sq (t := t) hθ.le
  have hp := n16Rad_pos (t := t) hθ
  unfold n16Psi
  have hh : 0 < 1-t-θ+n16Rad θ t := by nlinarith
  exact div_pos hh (by norm_num)

theorem n16PsiDeriv_eq {θ t : ℝ} (hθ : 0 < θ) :
    n16PsiDeriv θ t = -n16Psi θ t/n16Rad θ t := by
  unfold n16PsiDeriv n16Psi
  field_simp [(n16Rad_pos (t := t) hθ).ne']
  ring

theorem n16PsiDeriv_neg {θ t : ℝ} (hθ : 0 < θ) : n16PsiDeriv θ t < 0 := by
  rw [n16PsiDeriv_eq hθ]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (n16Psi_pos hθ)) (n16Rad_pos hθ)

noncomputable def n16LogDeriv (θ t : ℝ) : ℝ := Real.log (n16Psi θ t)-Real.log (n16Rad θ t)
noncomputable def n16LogDerivPrime (θ t : ℝ) : ℝ := (1-t-θ)/(n16Rad θ t)^2-1/n16Rad θ t

theorem n16LogDeriv_deriv {θ t : ℝ} (hθ : 0 < θ) :
    HasDerivAt (n16LogDeriv θ) (n16LogDerivPrime θ t) t := by
  have hh := ((n16Psi_deriv (t := t) hθ).log (n16Psi_pos hθ).ne').sub
    ((n16Rad_deriv (t := t) hθ).log (n16Rad_pos hθ).ne')
  convert hh using 1
  · rfl
  · dsimp [n16LogDerivPrime]
    rw [n16PsiDeriv_eq hθ]
    field_simp [(n16Psi_pos (t := t) hθ).ne', (n16Rad_pos (t := t) hθ).ne']
    ring

theorem n16LogDeriv_deriv2 {θ t : ℝ} (hθ : 0 < θ) :
    HasDerivAt (n16LogDerivPrime θ)
      (((1-t-θ)^2-(1-t-θ)*n16Rad θ t-4*θ)/(n16Rad θ t)^4) t := by
  have hs := ((hasDerivAt_id t).const_sub 1).sub_const θ
  have hr := n16Rad_deriv (t := t) hθ
  have hh := (hs.div (hr.pow 2) (pow_ne_zero _ (n16Rad_pos hθ).ne')).sub
    ((hasDerivAt_const t 1).div hr (n16Rad_pos hθ).ne')
  convert hh using 1
  · rfl
  · dsimp
    have he := n16Rad_sq (t := t) hθ.le
    field_simp [(n16Rad_pos (t := t) hθ).ne']
    nlinarith

theorem n16LogDeriv_convex {θ : ℝ} (hθ : 3 ≤ θ) : ConvexOn ℝ (Ioi 0) (n16LogDeriv θ) := by
  have hp : 0 < θ := by linarith
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
  · intro t _; exact (n16LogDeriv_deriv hp).continuousAt.continuousWithinAt
  · intro t _; exact (n16LogDeriv_deriv hp).hasDerivWithinAt
  · intro t _; exact (n16LogDeriv_deriv2 hp).hasDerivWithinAt
  · intro t ht
    have ht0 : 0 < t := interior_subset ht
    let x : ℝ := -(1-t-θ)
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hxθ : θ-1 ≤ x := by dsimp [x]; linarith
    have hθpoly := mul_nonneg (show 0 ≤ 3*θ-1 by linarith) (show 0 ≤ θ-3 by linarith)
    have hxx : 4*θ ≤ 3*x^2 := by nlinarith
    have hr := n16Rad_pos (t := t) hp
    have he : (n16Rad θ t)^2 = x^2+4*θ := by dsimp [x]; nlinarith [n16Rad_sq (t := t) hp.le]
    have he' := congrArg (fun y : ℝ => x^2*y) he
    have hprod := mul_nonneg (show 0 ≤ 4*θ by linarith) (show 0 ≤ 3*x^2-4*θ by linarith)
    have hsq : (4*θ-x^2)^2 ≤ (x*n16Rad θ t)^2 := by nlinarith [he']
    have hpos := mul_nonneg hx hr.le
    have hn : 0 ≤ x^2+x*n16Rad θ t-4*θ := by nlinarith
    apply div_nonneg _ (pow_nonneg hr.le _)
    dsimp [x] at hn
    nlinarith

theorem n16PsiDeriv_logconvex {θ : ℝ} (hθ : 3 ≤ θ) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-n16PsiDeriv θ t)) := by
  have hp : 0 < θ := by linarith
  apply (n16LogDeriv_convex hθ).congr
  intro t _
  dsimp only
  rw [n16PsiDeriv_eq hp, neg_div, neg_neg,
    Real.log_div (n16Psi_pos hp).ne' (n16Rad_pos hp).ne']
  rfl

theorem nelsen16_isCI {θ : ℝ} (hθ : 3 ≤ θ) : (nelsen16 θ (by linarith)).IsCI := by
  have hp : 0 < θ := by linarith
  let φ : ℝ → ℝ := fun u => (1-u)*(1+θ/u)
  let φ' : ℝ → ℝ := fun u => -1-θ/u^2
  have hh : (nelsen16Generator θ hp).copula.IsCI := by
    apply generator_isCI_of_logconvex_neg_deriv (nelsen16Generator θ hp) φ φ' (n16PsiDeriv θ)
    · intro u _ _; rfl
    · intro u hu
      exact mul_pos (sub_pos.mpr hu.2) (add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hp.le hu.1.le))
    · intro u hu
      have hd := ((hasDerivAt_id u).const_sub 1).mul
        (((hasDerivAt_const u θ).div (hasDerivAt_id u) hu.1.ne').const_add 1)
      convert hd using 1
      · rfl
      · dsimp [φ']; field_simp [hu.1.ne']; ring
    · intro t _; exact n16Psi_deriv hp
    · intro t _; exact n16PsiDeriv_neg hp
    · exact n16PsiDeriv_logconvex hθ
  simpa only [nelsen16, hp.ne', dite_false] using hh

theorem nelsen16_schur_monotone {θ η : ℝ} (hθ : 3 ≤ θ) (hη : 3 ≤ η) (hθη : θ ≤ η) :
    (nelsen16 θ (by linarith)).SchurBothLE (nelsen16 η (by linarith)) := by
  have ho := nelsen16_lowerOrthant_monotone (by linarith : 0 ≤ θ) (by linarith : 0 ≤ η) hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen16_isCI hθ).1 (nelsen16_isCI hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen16_isCI hθ).2 (nelsen16_isCI hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
