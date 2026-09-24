import Verification.Nelsen21Comparison
import Copula.Order.Orthant

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem n21Comparison_inv {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (u : I) :
    n21Comparison θ η ((n21Generator θ hθ).invFun u) = (n21Generator η hη).invFun u := by
  change n21Comparison θ η (n21Core θ u) = n21Core η u
  rw [n21Comparison_core (by linarith : 0 < θ) (n21Core_mem (by linarith) u.property),
    n21Core_involutive (by linarith : 0 < θ) u.property]

theorem n21Comparison_psi {θ η t : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (ht : t ∈ Icc 0 1) :
    n21Psi η (n21Comparison θ η t) = n21Psi θ t := by
  have hp : 0 < θ := by linarith
  have hq : 0 < η := by linarith
  rw [n21Comparison_core hp ht]
  unfold n21Psi
  rw [min_eq_left (n21Core_mem hq (n21Core_mem hp ht)).2,
    n21Core_involutive hq (n21Core_mem hp ht),min_eq_left ht.2]

theorem nelsen21_lowerOrthant_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hθη : θ ≤ η) :
    (nelsen21 θ hθ).LowerOrthantLE (nelsen21 η (hθ.trans hθη)) := by
  have hη := hθ.trans hθη
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  by_cases hz : x 0 = 0 ∨ x 1 = 0
  · rw [hx,nelsen21_cdf,nelsen21_cdf]
    simp only [hz,ite_true]
    exact le_rfl
  have hu : x 0 ≠ 0 := (not_or.mp hz).1
  have hv : x 1 ≠ 0 := (not_or.mp hz).2
  have hs := (n21Generator θ hθ).inv_nonneg (x 0) hu
  have ht := (n21Generator θ hθ).inv_nonneg (x 1) hv
  by_cases hsum : (n21Generator θ hθ).invFun (x 0)+(n21Generator θ hθ).invFun (x 1) ≤ 1
  · have hh := n21Comparison_superadd hθ hθη hs ht hsum
    rw [n21Comparison_inv hθ hη (x 0),n21Comparison_inv hθ hη (x 1)] at hh
    have hn := add_nonneg ((n21Generator η hη).inv_nonneg (x 0) hu) ((n21Generator η hη).inv_nonneg (x 1) hv)
    have hi := (n21Generator η hη).antitone hn (hn.trans hh) hh
    change n21Psi η (n21Comparison θ η _) ≤ _ at hi
    rw [n21Comparison_psi hθ hη ⟨add_nonneg hs ht,hsum⟩] at hi
    rw [hx]
    simp only [nelsen21,BivariateGenerator.cdf_copula,BivariateGenerator.cdf,
      Matrix.cons_val_zero,Matrix.cons_val_one,hu,hv,or_self,ite_false]
    exact hi
  · have he : (nelsen21 θ hθ).cdf x = 0 := by
      rw [hx]
      simp only [nelsen21,BivariateGenerator.cdf_copula,BivariateGenerator.cdf,
        Matrix.cons_val_zero,Matrix.cons_val_one,hu,hv,or_self,ite_false]
      change n21Psi θ ((n21Generator θ hθ).invFun (x 0)+(n21Generator θ hθ).invFun (x 1)) = 0
      unfold n21Psi
      rw [min_eq_right (lt_of_not_ge hsum).le]
      simp [n21Core,Real.zero_rpow (by linarith : θ ≠ 0)]
    rw [he]
    exact (nelsen21 η hη).cdf_nonneg x

end Verification
