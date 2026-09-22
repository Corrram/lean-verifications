import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact constant-displacement permutations at reciprocal-even means -/

namespace Verification

/-- Swap the two consecutive blocks of length k. -/
def halfBlockSwap (k : ℕ) : Equiv.Perm (Fin (k+k)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumComm (Fin k) (Fin k)).trans finSumFinEquiv)

theorem halfBlockSwap_distance (k : ℕ) (i : Fin (k+k)) :
    |(halfBlockSwap k i : ℝ)-(i : ℝ)| = k := by
  obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective i
  simp only [halfBlockSwap,Equiv.trans_apply,Equiv.symm_apply_apply]
  rcases j with j | j
  · change |((k+(j : ℕ) : ℕ) : ℝ)-(j : ℝ)| = (k : ℝ)
    rw [Nat.cast_add,add_sub_cancel_right,abs_of_nonneg (Nat.cast_nonneg k)]
  · change |(j : ℝ)-((k+(j : ℕ) : ℕ) : ℝ)| = (k : ℝ)
    rw [Nat.cast_add,show (j : ℝ)-((k : ℝ)+(j : ℝ)) = -(k : ℝ) by ring,
      abs_neg,abs_of_nonneg (Nat.cast_nonneg k)]

/-- Repeat the block swap in N consecutive groups. -/
def repeatedHalfBlockSwap (N k : ℕ) : Equiv.Perm (Fin (N*(k+k))) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin N)) (halfBlockSwap k)).trans finProdFinEquiv)

theorem repeatedHalfBlockSwap_distance (N k : ℕ) (i : Fin (N*(k+k))) :
    |(repeatedHalfBlockSwap N k i : ℝ)-(i : ℝ)| = k := by
  obtain ⟨⟨b,j⟩,rfl⟩ := finProdFinEquiv.surjective i
  simp only [repeatedHalfBlockSwap,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.prodCongr_apply]
  change |(((halfBlockSwap k j : ℕ)+(k+k)*(b : ℕ) : ℕ) : ℝ)-(((j : ℕ)+(k+k)*(b : ℕ) : ℕ) : ℝ)| = (k : ℝ)
  push_cast
  convert halfBlockSwap_distance k j using 1
  congr 1
  ring

/-- The integrality condition in Remark 2.2, for arbitrary positive ranking size. -/
theorem exists_constant_displacement_permutation_iff (n N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    (∃ π : Equiv.Perm (Fin n), ∀ i, |(π i : ℝ)-(i : ℝ)| = (n : ℝ)/(2*(N : ℝ))) ↔ 2*N ∣ n := by
  constructor
  · rintro ⟨π,hπ⟩
    let i : Fin n := ⟨0,hn⟩
    have he := hπ i
    have hi : (i : ℝ)=0 := by norm_num [i]
    rw [hi,sub_zero,abs_of_nonneg (Nat.cast_nonneg (π i : ℕ))] at he
    have hpos : (0 : ℝ) < 2*(N : ℝ) := by positivity
    have he' : (n : ℝ)=2*(N : ℝ)*(π i : ℝ) := by
      have h := (eq_div_iff hpos.ne').mp he
      linarith
    refine ⟨(π i : ℕ),?_⟩
    exact_mod_cast he'
  · rintro ⟨k,hk⟩
    have hsize : n=N*(k+k) := by rw [hk]; ring
    let e : Fin n ≃ Fin (N*(k+k)) := finCongr hsize
    let π : Equiv.Perm (Fin n) := e.trans ((repeatedHalfBlockSwap N k).trans e.symm)
    have hdist (i : Fin n) : |(π i : ℝ)-(i : ℝ)| = k := by
      convert repeatedHalfBlockSwap_distance N k (e i) using 1
      simp [π,e]
    refine ⟨π,fun i => (hdist i).trans ?_⟩
    have hpos : (0 : ℝ) < 2*(N : ℝ) := by positivity
    apply (eq_div_iff hpos.ne').mpr
    have hk' : (n : ℝ)=2*(N : ℝ)*(k : ℝ) := by exact_mod_cast hk
    nlinarith only [hk']

end Verification
