import Mathlib.Algebra.BigOperators.Module
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Verification

/-- Summation by parts against a decreasing sequence and nonnegative partial sums. -/
theorem decreasing_weighted_sum_nonneg (f g : ℕ → ℝ) (n : ℕ)
    (hf : ∀ i, i < n-1 → f (i+1) ≤ f i)
    (hg : ∀ k, k ≤ n → 0 ≤ ∑ i ∈ Finset.range k, g i)
    (ht : (∑ i ∈ Finset.range n, g i)=0) :
    0 ≤ ∑ i ∈ Finset.range n, f i*g i := by
  have he := Finset.sum_range_by_parts f g n
  simp only [smul_eq_mul] at he
  rw [he,ht,mul_zero,zero_sub]
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro i hi
  have hi' := Finset.mem_range.mp hi
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hf i hi')) (hg (i+1) (by omega))

/-- The quadratic Karamata inequality needed in the checkerboard comparison. -/
theorem majorization_sum_sq (a b : ℕ → ℝ) (n : ℕ)
    (hb : ∀ i, i < n-1 → b (i+1) ≤ b i)
    (hp : ∀ k, k ≤ n → (∑ i ∈ Finset.range k, b i) ≤ ∑ i ∈ Finset.range k, a i)
    (ht : (∑ i ∈ Finset.range n, a i) = ∑ i ∈ Finset.range n, b i) :
    (∑ i ∈ Finset.range n, b i^2) ≤ ∑ i ∈ Finset.range n, a i^2 := by
  have hw := decreasing_weighted_sum_nonneg b (fun i => a i-b i) n hb
    (fun k hk => by simpa only [Finset.sum_sub_distrib] using sub_nonneg.mpr (hp k hk))
    (by simp only [Finset.sum_sub_distrib,ht,sub_self])
  have hs : 0 ≤ ∑ i ∈ Finset.range n, (a i-b i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have he (i : ℕ) : (a i-b i)^2 = a i^2-b i^2-2*(b i*(a i-b i)) := by ring
  simp_rw [he] at hs
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hs
  linarith

end Verification
