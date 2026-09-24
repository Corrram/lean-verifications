import Verification.Nelsen20Comparison
import Verification.Nelsen20Limits
import Verification.Nelsen20Conditional
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem n20Comparison_inv {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (u : I) (hu : u ≠ 0) :
    n20Comparison θ η ((nelsen20Generator θ hθ).invFun u) = (nelsen20Generator η hη).invFun u := by
  have hp : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
  change Real.exp (Real.log ((Real.exp ((u:ℝ)^(-θ))-Real.exp 1)+Real.exp 1)^(η/θ))-Real.exp 1 = _
  rw [sub_add_cancel, Real.log_exp, ← Real.rpow_mul hp.le,
    show -θ*(η/θ) = -η by field_simp]
  rfl

theorem n20Comparison_psi {θ η t : ℝ} (hθ : 0 < θ) (hη : 0 < η) (ht : 0 ≤ t) :
    n20Psi η⁻¹ (n20Comparison θ η t) = n20Psi θ⁻¹ t := by
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  unfold n20Psi n20Comparison n20PowerExp
  rw [sub_add_cancel, Real.log_exp, ← Real.rpow_mul hl.le]
  congr 1
  field_simp

theorem nelsen20_lowerOrthant_monotone_pos {θ η : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hθη : θ ≤ η) :
    (nelsen20 θ hθ.le).LowerOrthantLE (nelsen20 η hη.le) := by
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  by_cases hz : x 0 = 0 ∨ x 1 = 0
  · rw [hx, nelsen20_cdf hθ, nelsen20_cdf hη]
    simp only [hz, ite_true]
    exact le_rfl
  have hu : x 0 ≠ 0 := (not_or.mp hz).1
  have hv : x 1 ≠ 0 := (not_or.mp hz).2
  have hs := (nelsen20Generator θ hθ).inv_nonneg (x 0) hu
  have ht := (nelsen20Generator θ hθ).inv_nonneg (x 1) hv
  have hh := n20Comparison_superadd hθ hθη hs ht
  rw [n20Comparison_inv hθ hη (x 0) hu, n20Comparison_inv hθ hη (x 1) hv] at hh
  have hn := add_nonneg ((nelsen20Generator η hη).inv_nonneg (x 0) hu)
    ((nelsen20Generator η hη).inv_nonneg (x 1) hv)
  have hi := (n20Psi_antitone (inv_pos.mpr hη)) hn (hn.trans hh) hh
  rw [n20Comparison_psi hθ hη (add_nonneg hs ht)] at hi
  rw [hx]
  simp only [nelsen20, hθ.ne', hη.ne', dite_false, BivariateGenerator.cdf_copula,
    BivariateGenerator.cdf, Matrix.cons_val_zero, Matrix.cons_val_one, hu, hv, or_self, ite_false]
  exact hi

theorem nelsen20_lowerOrthant_monotone {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (nelsen20 θ hθ).LowerOrthantLE (nelsen20 η hη) := by
  by_cases hz : θ = 0
  · subst θ
    by_cases he : η = 0
    · subst η; exact fun _ => le_rfl
    have hp : 0 < η := lt_of_le_of_ne hη (Ne.symm he)
    let p : ℕ → ℝ := fun n => η/((n:ℝ)+1)
    have hp' (n : ℕ) : 0 < p n := div_pos hp (by positivity)
    have ht : Tendsto p atTop (𝓝 0) := by
      simpa [p, div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, nelsen20_zero]
    apply le_of_tendsto (nelsen20_tendsto_zero p (fun n => (hp' n).le) ht (x 0) (x 1))
    apply Eventually.of_forall
    intro n
    apply nelsen20_lowerOrthant_monotone_pos (hp' n) hp _
    exact (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  · exact nelsen20_lowerOrthant_monotone_pos (lt_of_le_of_ne hθ (Ne.symm hz))
      (lt_of_lt_of_le (lt_of_le_of_ne hθ (Ne.symm hz)) hθη) hθη

theorem nelsen20_schur_monotone {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (nelsen20 θ hθ).SchurBothLE (nelsen20 η hη) := by
  have ho := nelsen20_lowerOrthant_monotone hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen20_isCI θ hθ).1 (nelsen20_isCI η hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen20_isCI θ hθ).2 (nelsen20_isCI η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
