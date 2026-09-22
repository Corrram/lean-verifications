import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Sort
import Mathlib.Tactic

namespace Verification

/-- Comparison count of the standard stable merge procedure. -/
def mergeComparisons {α : Type*} (le : α → α → Bool) : List α → List α → ℕ
  | [], _ => 0
  | _, [] => 0
  | x::xs, y::ys => if le x y then 1+mergeComparisons le xs (y::ys) else 1+mergeComparisons le (x::xs) ys
termination_by xs ys => xs.length+ys.length

theorem mergeComparisons_le {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    mergeComparisons le xs ys ≤ xs.length+ys.length := by
  fun_induction mergeComparisons le xs ys <;> simp_all only [List.length_cons,List.length_nil] <;> omega

/-- Work in merge-sort recursion: merge comparisons plus two linear traversals
per split/merge level. Input comparisons have unit cost, as in the paper. -/
def mergeSortWork {α : Type*} (le : α → α → Bool) : List α → ℕ
  | [] => 0
  | [_] => 0
  | a::b::xs =>
    let lr := List.MergeSort.Internal.splitInTwo ⟨a::b::xs,rfl⟩
    have h1 : lr.1.val.length < xs.length+1+1 := by rw [lr.1.property]; simp only [List.length_cons]; omega
    have h2 : lr.2.val.length < xs.length+1+1 := by rw [lr.2.property]; simp only [List.length_cons]; omega
    mergeSortWork le lr.1.val+mergeSortWork le lr.2.val+
      mergeComparisons le (lr.1.val.mergeSort le) (lr.2.val.mergeSort le)+2*(xs.length+2)
termination_by xs => xs.length

/-- Each balanced level costs at most three times the input length. -/
theorem mergeSortWork_le_depth {α : Type*} (le : α → α → Bool) (d : ℕ) (xs : List α)
    (h : xs.length ≤ 2^d) : mergeSortWork le xs ≤ 3*xs.length*d := by
  induction d generalizing xs with
  | zero =>
    have hx : xs.length≤1 := by simpa using h
    cases xs with
    | nil => simp [mergeSortWork]
    | cons a xs =>
      cases xs with
      | nil => simp [mergeSortWork]
      | cons b xs => simp only [List.length_cons] at hx; omega
  | succ d ih =>
    cases xs with
    | nil => simp [mergeSortWork]
    | cons a xs =>
      cases xs with
      | nil => simp [mergeSortWork]
      | cons b xs =>
        let lr := List.MergeSort.Internal.splitInTwo ⟨a::b::xs,rfl⟩
        have hl : lr.1.val.length=(xs.length+3)/2 := by exact lr.1.property
        have hr : lr.2.val.length=(xs.length+2)/2 := by exact lr.2.property
        have hpow : xs.length+2 ≤ 2*2^d := by simp only [List.length_cons,pow_succ] at h; omega
        have h1 := ih lr.1.val (by rw [hl]; omega)
        have h2 := ih lr.2.val (by rw [hr]; omega)
        have hm := mergeComparisons_le le (lr.1.val.mergeSort le) (lr.2.val.mergeSort le)
        simp only [List.length_mergeSort] at hm
        have hsum : lr.1.val.length+lr.2.val.length=xs.length+2 := by rw [hl,hr]; omega
        rw [mergeSortWork]
        change mergeSortWork le lr.1.val+mergeSortWork le lr.2.val+
          mergeComparisons le (lr.1.val.mergeSort le) (lr.2.val.mergeSort le)+2*(xs.length+2) ≤ _
        simp only [List.length_cons]
        nlinarith

theorem mergeSortWork_le {α : Type*} (le : α → α → Bool) (xs : List α) :
    mergeSortWork le xs ≤ 3*xs.length*Nat.clog 2 xs.length :=
  mergeSortWork_le_depth le _ xs (Nat.le_pow_clog (by omega) _)

end Verification
