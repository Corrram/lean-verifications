import Papers.Rockel2025Approximation.Definitions
import Verification.PermutationShuffle

/-! # Proposition 3.2: all equal-width straight permutation shuffles

The source's positive order N is represented as n+1, with zero-based indices.
Thus the source's endpoint conditions π(1)=1 and π(N)=N become π(0)=0
and π(Fin.last n)=Fin.last n. No symmetry assumption is imposed on π.
-/

open ProbabilityTheory
open scoped unitInterval

namespace Papers.Rockel2025Approximation

noncomputable def permutationShuffle (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) : Copula 2 :=
  Verification.PermutationShuffle.copula n π

/-- Number of pairs j<i with π(j)>π(i), equivalent to the source's inversion count. -/
def permutationInversions (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) : ℕ :=
  Verification.PermutationShuffle.inversions n π

theorem permutationShuffle_cdf (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (u v : I) :
    (permutationShuffle n π).cdf ![u, v] =
      ∑ i : Fin (n + 1),
        min (Verification.stripCut (1 / ((n : ℝ) + 1)) ((i : ℝ) / (n + 1)) u)
          (Verification.stripCut (1 / ((n : ℝ) + 1)) ((π i : ℝ) / (n + 1)) v) :=
  Verification.PositiveShuffle.cdf (Verification.PermutationShuffle.shuffle n π) ![u, v]

theorem permutationShuffle_rho (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (permutationShuffle n π).spearmanRho =
      1 - 6 * (∑ i : Fin (n + 1), ((π i : ℝ) - i) ^ 2) / ((n : ℝ) + 1) ^ 3 :=
  Verification.PermutationShuffle.rho n π

theorem permutationShuffle_tau (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (permutationShuffle n π).kendallTau =
      1 - 4 * (permutationInversions n π : ℝ) / ((n : ℝ) + 1) ^ 2 :=
  Verification.PermutationShuffle.tau n π

theorem permutationShuffle_xi (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (permutationShuffle n π).chatterjeeXi = 1 :=
  Verification.PermutationShuffle.xi n π

theorem permutationShuffle_lower_tail (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (permutationShuffle n π).HasLowerTailDependence (if π 0 = 0 then 1 else 0) :=
  Verification.PermutationShuffle.lower_tail n π

theorem permutationShuffle_upper_tail (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (permutationShuffle n π).HasUpperTailDependence
      (if π (Fin.last n) = Fin.last n then 1 else 0) :=
  Verification.PermutationShuffle.upper_tail n π

end Papers.Rockel2025Approximation
