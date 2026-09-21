import Papers.Rockel2026XiFootrule.Definitions
import Copula.Rank.FrechetOptimization

/-! # Exact Frechet-family minimum in Table 2

The weights a and b multiply M and W. The unique minimizer has a=0,b=1/4,
so the independence weight in the source's prose convention is 3/4.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

theorem frechet_coefficients (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).chatterjeeXi = (a - b) ^ 2 + a * b ∧
      (Copula.frechet a b ha hb hab).spearmanFootrule = a - b / 2 :=
  ⟨Copula.chatterjeeXi_frechet a b ha hb hab, Copula.spearmanFootrule_frechet a b ha hb hab⟩

theorem frechet_objective_lower (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    -(1 / 16 : ℝ) ≤ (Copula.frechet a b ha hb hab).chatterjeeXi +
      (Copula.frechet a b ha hb hab).spearmanFootrule :=
  Copula.frechet_xi_add_footrule_lower a b ha hb hab

theorem frechet_objective_eq_iff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (Copula.frechet a b ha hb hab).chatterjeeXi +
      (Copula.frechet a b ha hb hab).spearmanFootrule = -(1 / 16 : ℝ) ↔
        a = 0 ∧ b = 1 / 4 :=
  Copula.frechet_xi_add_footrule_eq_iff a b ha hb hab

theorem frechet_minimizer_coefficients :
    (Copula.frechet 0 (1 / 4) (by norm_num) (by norm_num) (by norm_num)).chatterjeeXi = 1 / 16 ∧
    (Copula.frechet 0 (1 / 4) (by norm_num) (by norm_num) (by norm_num)).spearmanFootrule = -1 / 8 := by
  rw [Copula.chatterjeeXi_frechet, Copula.spearmanFootrule_frechet]
  norm_num

end Papers.Rockel2026XiFootrule
