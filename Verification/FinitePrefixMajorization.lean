import Verification.FiniteMajorization

open scoped BigOperators

namespace Verification

noncomputable def extendFin {n : ℕ} (a : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : i < n then a ⟨i,hi⟩ else 0

theorem sum_extendFin_prefix {n : ℕ} (a : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    (∑ i : Fin n, if i.val < k then a i else 0) = ∑ i ∈ Finset.range k, extendFin a i := by
  rw [Finset.sum_fin_eq_sum_range]
  calc
    _ = ∑ i ∈ Finset.range n, if i < k then extendFin a i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_range] at hi
      simp only [hi,dite_eq_left,extendFin]
    _ = ∑ i ∈ Finset.range k, if i < k then extendFin a i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i _ hi
      simp only [Finset.mem_range] at hi
      simp only [hi,ite_false]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left (Finset.mem_range.mp hi)]

theorem majorization_fin_sum_sq {n : ℕ} (a b : Fin n → ℝ) (hb : Antitone b)
    (hp : ∀ k : Fin (n+1),
      (∑ i : Fin n, if i.val < k.val then b i else 0) ≤ ∑ i : Fin n, if i.val < k.val then a i else 0)
    (ht : (∑ i, a i) = ∑ i, b i) :
    (∑ i, b i^2) ≤ ∑ i, a i^2 := by
  have h := majorization_sum_sq (extendFin a) (extendFin b) n (by
    intro i hi
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [extendFin,dite_eq_left hi0,dite_eq_left hi1]
    exact hb (show (⟨i,hi0⟩ : Fin n) ≤ ⟨i+1,hi1⟩ by simp)) (by
    intro k hk
    simpa only [← sum_extendFin_prefix b k hk,← sum_extendFin_prefix a k hk] using hp ⟨k,by omega⟩) (by
    simpa only [Finset.sum_fin_eq_sum_range,extendFin] using ht)
  rw [← Fin.sum_univ_eq_sum_range (fun i => extendFin b i^2) n,
    ← Fin.sum_univ_eq_sum_range (fun i => extendFin a i^2) n] at h
  simpa only [extendFin,dite_eq_left (Fin.is_lt _)] using h

end Verification
