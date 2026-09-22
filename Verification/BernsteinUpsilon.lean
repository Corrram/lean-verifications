import Verification.BernsteinUpsilonInterior
import Verification.BernsteinUpsilonBoundary
import Verification.BernsteinTauTrace

open MeasureTheory ProbabilityTheory Matrix
open scoped unitInterval BigOperators

namespace Verification

/-- The source's piecewise Upsilon matrix for degree n+1, with source indices i+1,r+1. -/
noncomputable def bernsteinUpsilonMatrix (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  Matrix.of fun i r =>
    if i=Fin.last n then
      if r=Fin.last n then ((n : ℝ)+1)^2/(2*(n : ℝ)+1)
      else (((n : ℝ)+1)*(n : ℝ)*((r : ℝ)-(n : ℝ))*((n+1).choose (r.val+1) : ℝ)) /
        ((2*(n : ℝ)+1)*(2*(n : ℝ))*((2*n-1).choose (n+r.val) : ℝ))
    else if r=Fin.last n then
      (((n : ℝ)+1)*(n : ℝ)*((i : ℝ)-(n : ℝ))*((n+1).choose (i.val+1) : ℝ)) /
        ((2*(n : ℝ)+1)*(2*(n : ℝ))*((2*n-1).choose (n+i.val) : ℝ))
    else (((n+1).choose (i.val+1) : ℝ)*((n+1).choose (r.val+1) : ℝ)) /
      ((2*(n : ℝ)-1)*((2*n-2).choose (i.val+r.val) : ℝ)) *
      (((i : ℝ)+1)*((r : ℝ)+1) -
        (2*((n : ℝ)+1)*(n : ℝ)*((i.val+r.val+2).choose 2 : ℝ))/((2*(n : ℝ)+1)*(2*(n : ℝ))))

theorem bernsteinUpsilonMatrix_integral (n : ℕ) (i r : Fin (n+1)) :
    (∫ u : I, bernsteinDerivative (n+1) (i.val+1) u * bernsteinDerivative (n+1) (r.val+1) u) =
      bernsteinUpsilonMatrix n i r := by
  by_cases hi : i=Fin.last n
  · subst i
    by_cases hr : r=Fin.last n
    · subst r
      simpa [bernsteinUpsilonMatrix] using bernstein_upsilon_corner n
    · have hr' : r.val < n := by
        have hne : r.val ≠ n := fun h => hr (Fin.ext h)
        omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have h := bernstein_upsilon_boundary k r (by omega)
      rw [integral_congr_ae (Filter.Eventually.of_forall (fun u : I => mul_comm _ _))]
      convert h using 1
      · simp only [Fin.val_last,Nat.succ_eq_add_one,Nat.add_assoc]
      · simp only [bernsteinUpsilonMatrix,Matrix.of_apply,ite_true,ite_false,hr,
          Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,
          show 2*(k+1)-1=2*k+1 by omega,show k+1+r.val=k+r.val+1 by omega]
        congr 1 <;> ring
  · by_cases hr : r=Fin.last n
    · subst r
      have hi' : i.val < n := by
        have hne : i.val ≠ n := fun h => hi (Fin.ext h)
        omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have h := bernstein_upsilon_boundary k i (by omega)
      convert h using 1
      · simp only [Fin.val_last,Nat.succ_eq_add_one,Nat.add_assoc]
      · simp only [bernsteinUpsilonMatrix,Matrix.of_apply,ite_true,ite_false,hi,
          Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,
          show 2*(k+1)-1=2*k+1 by omega,show k+1+i.val=k+i.val+1 by omega]
        congr 1 <;> ring
    · have hi' : i.val < n := by
        have hne : i.val ≠ n := fun h => hi (Fin.ext h)
        omega
      have hr' : r.val < n := by
        have hne : r.val ≠ n := fun h => hr (Fin.ext h)
        omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have h := bernstein_upsilon_interior k i r (by omega) (by omega)
      convert h using 1
      simp only [bernsteinUpsilonMatrix,Matrix.of_apply,ite_false,hi,hr,
          Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,
          show 2*(k+1)-2=2*k by omega]
      congr 1 <;> ring

end Verification
