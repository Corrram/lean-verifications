import Verification.Nelsen20

open Set

namespace Verification

noncomputable def n20PowerExp (r t : ℝ) : ℝ := Real.exp (Real.log (t+Real.exp 1)^r)
noncomputable def n20PowerExpPrime (r t : ℝ) : ℝ :=
  r*Real.log (t+Real.exp 1)^(r-1)*n20PowerExp r t/(t+Real.exp 1)

theorem n20_log_ge_one {t : ℝ} (ht : 0 ≤ t) : 1 ≤ Real.log (t+Real.exp 1) := by
  have hh := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ t+Real.exp 1 by linarith)
  simpa only [Real.log_exp] using hh

theorem n20PowerExp_deriv {r t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (n20PowerExp r) (n20PowerExpPrime r t) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hh := ((((hasDerivAt_id t).add_const (Real.exp 1)).log hx.ne').rpow_const (p := r) (Or.inl hl.ne')).exp
  convert hh using 1
  · rfl
  · dsimp [n20PowerExpPrime, n20PowerExp]; ring

theorem n20PowerExp_deriv2 {r t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (n20PowerExpPrime r)
      (r*Real.log (t+Real.exp 1)^(r-2)*n20PowerExp r t*
        (r-1+Real.log (t+Real.exp 1)*(r*Real.log (t+Real.exp 1)^(r-1)-1))/(t+Real.exp 1)^2) t := by
  have hx : 0 < t+Real.exp 1 := add_pos_of_nonneg_of_pos ht (Real.exp_pos 1)
  have hl := n19_log_pos (by norm_num : (0:ℝ) < 1) ht
  have hd := (hasDerivAt_id t).add_const (Real.exp 1)
  have hh := ((((hd.log hx.ne').rpow_const (p := r-1) (Or.inl hl.ne')).const_mul r).mul
    (n20PowerExp_deriv (r := r) ht)).div hd hx.ne'
  have he : Real.log (t+Real.exp 1)^(r-1) = Real.log (t+Real.exp 1)^(r-2)*Real.log (t+Real.exp 1) := by
    rw [show r-1 = (r-2)+1 by ring, Real.rpow_add_one hl.ne']
  convert hh using 1
  · rfl
  · dsimp [n20PowerExpPrime]
    rw [show r-1-1 = r-2 by ring, he]
    field_simp
    ring

theorem n20PowerExp_convex {r : ℝ} (hr : 1 ≤ r) : ConvexOn ℝ (Ici 0) (n20PowerExp r) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t ht; exact (n20PowerExp_deriv ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n20PowerExp_deriv (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n20PowerExp_deriv2 (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have hl := n20_log_ge_one (interior_subset ht)
    have hl0 : 0 ≤ Real.log (t+Real.exp 1) := by linarith
    have hp : 1 ≤ Real.log (t+Real.exp 1)^(r-1) := Real.one_le_rpow hl (by linarith)
    have hprod : 1 ≤ r*Real.log (t+Real.exp 1)^(r-1) := by nlinarith
    have hn : 0 ≤ r-1+Real.log (t+Real.exp 1)*(r*Real.log (t+Real.exp 1)^(r-1)-1) :=
      add_nonneg (by linarith) (mul_nonneg hl0 (by linarith))
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hl0 _)) (Real.exp_pos _).le) hn

noncomputable def n20Comparison (θ η t : ℝ) : ℝ := n20PowerExp (η/θ) t-Real.exp 1

theorem n20Comparison_superadd {θ η s t : ℝ} (hθ : 0 < θ) (hθη : θ ≤ η)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    n20Comparison θ η s+n20Comparison θ η t ≤ n20Comparison θ η (s+t) := by
  have hr : 1 ≤ η/θ := (le_div_iff₀ hθ).mpr (by simpa using hθη)
  have hh := ProbabilityTheory.Copula.BivariateGenerator.convex_increment (n20PowerExp_convex hr)
    (show (0:ℝ) ≤ 0 from le_rfl) (show (0:ℝ) ≤ 0 from le_rfl) hs ht
  have hz : n20PowerExp (η/θ) 0 = Real.exp 1 := by simp [n20PowerExp]
  simp only [zero_add, add_zero, hz] at hh
  dsimp [n20Comparison]
  linarith

end Verification
