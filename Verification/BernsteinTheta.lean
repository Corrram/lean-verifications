import Verification.BernsteinMixedProducts

open MeasureTheory ProbabilityTheory
open scoped unitInterval BigOperators

namespace Verification

/-- Off-corner entries of the paper's Theta matrix equal twice the mixed derivative Gram entry. -/
theorem bernstein_theta_off_corner (k i r : ℕ) (hi : i ≤ k) (_hr : r ≤ k) (hir : i+r < 2*k) :
    2 * bernsteinMixedGram (k+1) i r =
      (((i : ℝ)-(r : ℝ)) * ((k+1).choose (i+1) : ℝ) * ((k+1).choose (r+1) : ℝ)) /
        ((2*(k : ℝ)-(i : ℝ)-(r : ℝ)) * ((2*k+1).choose (i+r+1) : ℝ)) := by
  have ha : ((k : ℝ)+1) * (k.choose i : ℝ) =
      ((i : ℝ)+1) * ((k+1).choose (i+1) : ℝ) := by
    have h := Nat.add_one_mul_choose_eq k i
    rw [mul_comm ((k+1).choose (i+1)) (i+1)] at h
    exact_mod_cast h
  have hb : (k.choose (i+1) : ℝ) * ((k : ℝ)+1) =
      ((k+1).choose (i+1) : ℝ) * ((k : ℝ)-(i : ℝ)) := by
    have h := Nat.choose_mul_succ_eq k (i+1)
    rw [Nat.add_sub_add_right] at h
    exact_mod_cast h
  have hc : (((2*k+1).choose (i+r+2) : ℝ) * ((i : ℝ)+(r : ℝ)+2)) =
      ((2*k+1).choose (i+r+1) : ℝ) * (2*(k : ℝ)-(i : ℝ)-(r : ℝ)) := by
    have h := Nat.choose_succ_right_eq (2*k+1) (i+r+1)
    rw [Nat.add_sub_add_right] at h
    have hreal := congrArg (fun z : ℕ => (z : ℝ)) h
    push_cast [Nat.cast_sub (by omega : i+r ≤ 2*k)] at hreal
    convert hreal using 1 <;> congr 1 <;> ring
  have h0 : ((2*k+1).choose (i+r+1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : i+r+1 ≤ 2*k+1)).ne'
  have h1 : ((2*k+1).choose (i+r+2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : i+r+2 ≤ 2*k+1)).ne'
  have hk : (2*(k : ℝ)+2) ≠ 0 := by positivity
  have hd : (2*(k : ℝ)-(i : ℝ)-(r : ℝ)) ≠ 0 := by
    have h : (i : ℝ)+(r : ℝ)<2*(k : ℝ) := by exact_mod_cast hir
    linarith
  simp only [bernsteinMixedGram,bernsteinGram,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  rw [show k+(k+1)=2*k+1 by omega,show i+(r+1)=i+r+1 by omega,
    show i+1+(r+1)=i+r+2 by omega]
  have hden : (k : ℝ)+((k : ℝ)+1)+1=2*(k : ℝ)+2 := by ring
  rw [hden]
  field_simp
  apply (mul_left_cancel₀ (by positivity : (k : ℝ)+1 ≠ 0))
  linear_combination
    (((k+1).choose (r+1) : ℝ) * ((2*k+1).choose (i+r+2) : ℝ) * (2*(k : ℝ)-(i : ℝ)-(r : ℝ))) * ha -
    (((k+1).choose (r+1) : ℝ) * ((2*k+1).choose (i+r+1) : ℝ) * (2*(k : ℝ)-(i : ℝ)-(r : ℝ))) * hb +
    (((k+1).choose (r+1) : ℝ) * ((k+1).choose (i+1) : ℝ) * ((k : ℝ)-(i : ℝ))) * hc

theorem bernstein_theta_corner (k : ℕ) : 2 * bernsteinMixedGram (k+1) k k = 1 := by
  simp only [bernsteinMixedGram,bernsteinGram,Nat.add_sub_cancel,Nat.choose_self,
    Nat.choose_succ_self,Nat.cast_one,Nat.cast_zero,zero_mul,zero_div,sub_zero,Nat.cast_add]
  simp only [mul_one]
  field_simp
  ring

/-- The source Theta matrix, with its special 0/0=1 convention at the last diagonal entry.
The degree is k+1 and indices are source indices i+1,r+1. -/
noncomputable def bernsteinTheta (k : ℕ) (i r : Fin (k+1)) : ℝ :=
  if i=Fin.last k ∧ r=Fin.last k then 1 else
    (((i : ℝ)-(r : ℝ)) * ((k+1).choose (i.val+1) : ℝ) * ((k+1).choose (r.val+1) : ℝ)) /
      ((2*(k : ℝ)-(i : ℝ)-(r : ℝ)) * ((2*k+1).choose (i.val+r.val+1) : ℝ))

theorem bernsteinTheta_eq_mixedGram (k : ℕ) (i r : Fin (k+1)) :
    bernsteinTheta k i r = 2 * bernsteinMixedGram (k+1) i r := by
  unfold bernsteinTheta
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    exact (bernstein_theta_corner k).symm
  · apply (bernstein_theta_off_corner k i r (by omega) (by omega) _).symm
    have hi : (i : ℕ) ≤ k := by omega
    have hr : (r : ℕ) ≤ k := by omega
    have hn : ¬ ((i : ℕ)=k ∧ (r : ℕ)=k) := by
      rintro ⟨hi,hr⟩
      exact h ⟨Fin.ext hi,Fin.ext hr⟩
    omega

theorem bernsteinTheta_add_transpose (k : ℕ) (i r : Fin (k+1)) :
    bernsteinTheta k i r + bernsteinTheta k r i =
      if i=Fin.last k ∧ r=Fin.last k then 2 else 0 := by
  unfold bernsteinTheta
  have he : (r=Fin.last k ∧ i=Fin.last k) ↔ (i=Fin.last k ∧ r=Fin.last k) := and_comm
  simp only [he]
  split_ifs
  · norm_num
  · rw [show r.val+i.val+1=i.val+r.val+1 by omega]
    ring

end Verification
