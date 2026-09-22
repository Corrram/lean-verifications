import Papers.AnsariRockel2026RhoFootrule.FiniteRankings
import Verification.ConstantDisplacementPermutation
import Verification.FiniteCauchyEquality

/-! # Exact finite-ranking equality at the reciprocal-even contact means -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval BigOperators

namespace Papers.AnsariRockel2026RhoFootrule

/-- Ordinary finite Cauchy--Schwarz is an equality precisely for constant absolute displacement. -/
theorem ranking_cauchy_equality_iff (n : ℕ) (π : Equiv.Perm (Fin (n+1))) :
    rankingSquare n π=(rankingDistance n π)^2/((n : ℝ)+1) ↔
      ∀ i, |(π i : ℝ)-(i : ℝ)|=rankingDistance n π/((n : ℝ)+1) := by
  simpa only [rankingSquare,rankingDistance,sq_abs,Nat.cast_add,Nat.cast_one] using
    finite_cauchy_equality_iff (n+1) (by omega) (fun i => |(π i : ℝ)-(i : ℝ)|)

/-- The displayed constant-displacement formulation in Remark 2.2. -/
theorem ranking_constant_contact_iff (n N : ℕ) (hN : 0 < N) :
    (∃ π : Equiv.Perm (Fin (n+1)), ∀ i,
      |(π i : ℝ)-(i : ℝ)|=((n : ℝ)+1)/(2*(N : ℝ))) ↔ 2*N ∣ n+1 := by
  simpa only [Nat.cast_add,Nat.cast_one] using
    exists_constant_displacement_permutation_iff (n+1) N (by omega) hN

/-- Remark 2.2: equality at mean 1/(2N) is possible exactly for divisible ranking sizes. -/
theorem ranking_contact_equality_exists_iff (n N : ℕ) (hN : 0 < N) :
    (∃ π : Equiv.Perm (Fin (n+1)),
      rankingDistance n π/((n : ℝ)+1)^2=1/(2*(N : ℝ)) ∧
      rankingSquare n π=(rankingDistance n π)^2/((n : ℝ)+1)) ↔ 2*N ∣ n+1 := by
  have hn0 : (n : ℝ)+1 ≠ 0 := by positivity
  have hN0 : (2*(N : ℝ)) ≠ 0 := by positivity
  constructor
  · rintro ⟨π,hm,he⟩
    apply (ranking_constant_contact_iff n N hN).mp
    have hd : rankingDistance n π/((n : ℝ)+1)=((n : ℝ)+1)/(2*(N : ℝ)) := by
      field_simp at hm ⊢
      nlinarith only [hm]
    exact ⟨π,fun i => ((ranking_cauchy_equality_iff n π).mp he i).trans hd⟩
  · intro h
    obtain ⟨π,hπ⟩ := (ranking_constant_contact_iff n N hN).mpr h
    have hD : rankingDistance n π=((n : ℝ)+1)*(((n : ℝ)+1)/(2*(N : ℝ))) := by
      simp only [rankingDistance,hπ,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
    refine ⟨π,?_,(ranking_cauchy_equality_iff n π).mpr ?_⟩
    · rw [hD]
      field_simp
    · intro i
      rw [hπ i,hD]
      field_simp

/-- Away from the reciprocal-even contact means, the finite correction is strictly positive. -/
theorem finite_ranking_strict_correction (n : ℕ) (π : Equiv.Perm (Fin (n+1)))
    (h0 : rankingDistance n π/((n : ℝ)+1)^2 ≠ 0)
    (hN : ∀ N : ℕ, 0 < N → rankingDistance n π/((n : ℝ)+1)^2 ≠ 1/(2*(N : ℝ))) :
    0 < minimumVariance (rankingDistance n π/((n : ℝ)+1)^2) ∧
      (rankingDistance n π)^2/((n : ℝ)+1) < rankingSquare n π := by
  have hm : rankingDistance n π/((n : ℝ)+1)^2 ∈ Set.Icc (0 : ℝ) (1/2) := by
    rw [← ranking_mean]
    exact meanDistance_mem _
  have hv : 0 < minimumVariance (rankingDistance n π/((n : ℝ)+1)^2) := by
    apply lt_of_le_of_ne (minimum_variance_nonneg hm)
    intro he
    rcases (minimum_variance_zero_iff hm).mp he.symm with hz | ⟨N,hp,he⟩
    · exact h0 hz
    · exact hN N hp he
  refine ⟨hv,?_⟩
  have hc := finite_ranking_cauchy_correction n π
  have hp : 0 < ((n : ℝ)+1)^3*minimumVariance (rankingDistance n π/((n : ℝ)+1)^2) :=
    mul_pos (by positivity) hv
  linarith

end Papers.AnsariRockel2026RhoFootrule
