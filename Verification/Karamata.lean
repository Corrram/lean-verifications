import Verification.FiniteMajorization
import Mathlib.Analysis.Convex.Deriv

open Set
open scoped BigOperators

namespace Verification

theorem convex_rightDeriv_support (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f) (x y : ℝ) :
    f x+derivWithin f (Ioi x) x*(y-x) ≤ f y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hh := hf.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ y) h
    rw [slope_def_field] at hh
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hh
    linarith
  · simp
  · have hh := (hf.slope_le_leftDeriv_of_mem_interior (mem_univ y) (by simp) h).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp : x ∈ interior (univ : Set ℝ)))
    rw [slope_def_field] at hh
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith

/-- Full Karamata inequality. Only the comparison vector needs to be decreasing. -/
theorem majorization_sum_convex (a b : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) (hf : ConvexOn ℝ univ f)
    (hb : ∀ i, i<n-1 → b (i+1)≤b i)
    (hp : ∀ k, k≤n → (∑ i ∈ Finset.range k, b i) ≤ ∑ i ∈ Finset.range k, a i)
    (ht : (∑ i ∈ Finset.range n, a i)=∑ i ∈ Finset.range n, b i) :
    (∑ i ∈ Finset.range n, f (b i)) ≤ ∑ i ∈ Finset.range n, f (a i) := by
  let d : ℕ → ℝ := fun i => derivWithin f (Ioi (b i)) (b i)
  have hd : ∀ i, i<n-1 → d (i+1)≤d i := by
    intro i hi
    exact hf.monotoneOn_rightDeriv (by simp) (by simp) (hb i hi)
  have hw := decreasing_weighted_sum_nonneg d (fun i => a i-b i) n hd
    (fun k hk => by simpa only [Finset.sum_sub_distrib] using sub_nonneg.mpr (hp k hk))
    (by simp only [Finset.sum_sub_distrib,ht,sub_self])
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range n) => convex_rightDeriv_support f hf (b i) (a i))
  change (∑ i ∈ Finset.range n, (f (b i)+d i*(a i-b i))) ≤ _ at hs
  rw [Finset.sum_add_distrib] at hs
  linarith

end Verification
