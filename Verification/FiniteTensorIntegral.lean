import Copula.Rank.Integration

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

namespace Verification

/-- Squared tensor expansions integrate into the contraction of two Gram matrices. -/
theorem integral_tensor_square {α β : Type*} [Fintype α] [Fintype β]
    (D : α → β → ℝ) (f : α → C(I,ℝ)) (g : β → C(I,ℝ)) :
    (∫ v : I, ∫ u : I, (∑ i, ∑ j, D i j * f i u * g j v)^2) =
      ∑ i, ∑ j, ∑ r, ∑ s, D i j * D r s *
        (∫ u : I, f i u * f r u) * (∫ v : I, g j v * g s v) := by
  have hs (u v : I) : (∑ i, ∑ j, D i j * f i u * g j v)^2 =
      ∑ i, ∑ j, ∑ r, ∑ s, (D i j * f i u * g j v) * (D r s * f r u * g s v) := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  have hint (i r : α) (j s : β) (v : I) :
      (∫ u : I, (D i j * f i u * g j v) * (D r s * f r u * g s v)) =
      (D i j * D r s * (∫ u : I, f i u * f r u)) * (g j v * g s v) := by
    have he (u : I) : D i j * f i u * g j v * (D r s * f r u * g s v) =
        (D i j * D r s * (g j v * g s v)) * (f i u * f r u) := by ring
    simp_rw [he,integral_const_mul]
    ring
  simp_rw [hs]
  simp (disch := intro i hi; exact Copula.integrable_continuous_unit volume (by fun_prop)) only
    [integral_finsetSum,hint,integral_const_mul]

end Verification
