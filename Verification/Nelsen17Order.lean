import Verification.Nelsen17Comparison
import Verification.Nelsen17Conditional
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

theorem nelsen17_lowerOrthant_monotone {θ η : ℝ}
    (hθ : θ ≠ 0) (hη : η ≠ 0) (hθη : θ ≤ η) :
    (nelsen17 θ hθ).LowerOrthantLE (nelsen17 η hη) := by
  have ha := neg_ne_zero.mpr hθ
  have hb := neg_ne_zero.mpr hη
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  by_cases hz : x 0 = 0 ∨ x 1 = 0
  · rw [hx, nelsen17_cdf, nelsen17_cdf]
    simp only [hz, ite_true]
    exact le_rfl
  have hu : x 0 ≠ 0 := (not_or.mp hz).1
  have hv : x 1 ≠ 0 := (not_or.mp hz).2
  have hs := (n17Generator (-θ) ha).inv_nonneg (x 0) hu
  have ht := (n17Generator (-θ) ha).inv_nonneg (x 1) hv
  have hh := n17Comparison_superadd ha hb (neg_le_neg hθη) hs ht
  rw [n17Comparison_inv ha hb (x 0) hu, n17Comparison_inv ha hb (x 1) hv] at hh
  have hn := add_nonneg ((n17Generator (-η) hb).inv_nonneg (x 0) hu)
    ((n17Generator (-η) hb).inv_nonneg (x 1) hv)
  have hi := (n17Psi_antitone hb) hn (hn.trans hh) hh
  rw [n17Comparison_psi ha hb (add_nonneg hs ht)] at hi
  rw [hx]
  simp only [nelsen17, BivariateGenerator.cdf_copula, BivariateGenerator.cdf,
    Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ite_false]
  exact hi

theorem nelsen17_schur_monotone {θ η : ℝ} (hθ : θ ≠ 0) (hη : η ≠ 0)
    (hθ1 : -1 ≤ θ) (hθη : θ ≤ η) :
    (nelsen17 θ hθ).SchurBothLE (nelsen17 η hη) := by
  have hη1 : -1 ≤ η := hθ1.trans hθη
  have ho := nelsen17_lowerOrthant_monotone hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen17_isCI θ hθ hθ1).1 (nelsen17_isCI η hη hη1).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen17_isCI θ hθ hθ1).2 (nelsen17_isCI η hη hη1).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_transpose,cdf_transpose]
    exact ho ![x 1,x 0]

theorem nelsen17_schur_antitone {θ η : ℝ} (hθ : θ ≠ 0) (hη : η ≠ 0)
    (hη1 : η ≤ -1) (hθη : θ ≤ η) :
    (nelsen17 η hη).SchurBothLE (nelsen17 θ hθ) := by
  have hθ1 : θ ≤ -1 := hθη.trans hη1
  have ho := nelsen17_lowerOrthant_monotone hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSD _ _ (nelsen17_isCD η hη hη1).1 (nelsen17_isCD θ hθ hθ1).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSD _ _ (nelsen17_isCD η hη hη1).2 (nelsen17_isCD θ hθ hθ1).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx,cdf_transpose,cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
