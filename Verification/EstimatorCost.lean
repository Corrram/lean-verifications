import Verification.MergeSortCost
import Verification.PowerGrid
import Verification.OverlapSparsity
import Mathlib.Analysis.SpecialFunctions.Log.Base

open Filter Asymptotics
open scoped Topology

namespace Verification

/-- Four explicit sparse update slots per observation. -/
def rankUpdateSlots (n : ℕ) : ℕ := Fintype.card (Fin n × Fin 2 × Fin 2)

/-- Number of scalar products in one dense K-by-K matrix multiplication. -/
def matrixProductSlots (K : ℕ) : ℕ := Fintype.card (Fin K × Fin K × Fin K)

theorem rankUpdateSlots_eq (n : ℕ) : rankUpdateSlots n=4*n := by simp [rankUpdateSlots]; omega

theorem matrixProductSlots_eq (K : ℕ) : matrixProductSlots K=K^3 := by simp [matrixProductSlots]; ring

/-- Unit-cost work for two rank sorts, four sparse updates per sample, and
three dense matrix products, initialization and traces. The factor 32 covers
scalar arithmetic and indexing in each slot of the explicit finite formulas. -/
def checkerboardEstimatorWork {α β : Type*} (leX : α → α → Bool) (leY : β → β → Bool)
    (xs : List α) (ys : List β) (K : ℕ) : ℕ :=
  mergeSortWork leX xs+mergeSortWork leY ys+
    32*(rankUpdateSlots xs.length+3*matrixProductSlots K+K^2+K+1)

theorem checkerboardEstimatorWork_bound {α β : Type*} (leX : α → α → Bool) (leY : β → β → Bool)
    (xs : List α) (ys : List β) (hxy : ys.length=xs.length) (K : ℕ) (hK : 0<K)
    (hKn : K^3≤xs.length) :
    checkerboardEstimatorWork leX leY xs ys K ≤ 6*xs.length*Nat.clog 2 xs.length+320*xs.length := by
  have hx := mergeSortWork_le leX xs
  have hy := mergeSortWork_le leY ys
  rw [hxy] at hy
  have hK1 : 1≤K := hK
  have hk2 : K^2≤K^3 := by nlinarith [sq_nonneg (K-1 : ℤ)]
  have hk : K≤K^3 := by nlinarith
  have hn : 1≤xs.length := by nlinarith
  unfold checkerboardEstimatorWork
  rw [rankUpdateSlots_eq,matrixProductSlots_eq]
  nlinarith

theorem nat_clog_two_le_log (n : ℕ) (hn : 2≤n) :
    (Nat.clog 2 n : ℝ) ≤ (2/Real.log 2)*Real.log (n : ℝ) := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn
  have hlog : Real.log 2≤Real.log (n : ℝ) := Real.log_le_log (by norm_num) hnR
  have hc := Nat.ceil_lt_add_one (a := Real.logb 2 (n : ℝ))
    (Real.logb_nonneg (by norm_num) (by linarith))
  have hec := congrArg (fun z : ℕ => (z : ℝ)) (Real.natCeil_logb_natCast 2 n)
  norm_num only [Nat.cast_ofNat] at hec
  rw [hec,Real.logb] at hc
  have hh := (div_le_div_iff_of_pos_right h2).mpr hlog
  have he : Real.log 2/Real.log 2=1 := div_self h2.ne'
  rw [he] at hh
  have hl : (Nat.clog 2 n : ℝ) ≤ 2*(Real.log (n : ℝ)/Real.log 2) := by linarith
  convert hl using 1
  ring

/-- The prescribed sparse/matrix work schedule is O(N log N) for the source's
power grid, with the standard unit-cost arithmetic and array-update convention. -/
theorem checkerboardEstimatorWork_isBigO {α β : Type*} (leX : α → α → Bool) (leY : β → β → Bool)
    (xs : ℕ → List α) (ys : ℕ → List β) (hx : ∀ n, (xs n).length=n+1) (hy : ∀ n, (ys n).length=n+1)
    (κ : ℝ) (hκ : 0≤κ) (hκ' : κ≤1/3) :
    (fun n => (checkerboardEstimatorWork leX leY (xs n) (ys n) (powerGridIndex κ n+1) : ℝ)) =O[atTop]
      (fun n => ((n : ℝ)+1)*Real.log ((n : ℝ)+1)) := by
  have h2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  apply Asymptotics.IsBigO.of_bound (332/Real.log 2)
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn2 : 2≤n+1 := by omega
  have hlog : Real.log 2≤Real.log ((n : ℝ)+1) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
  have hb := checkerboardEstimatorWork_bound leX leY (xs n) (ys n) (by rw [hx,hy])
    (powerGridIndex κ n+1) (by omega) (by rw [hx]; exact powerGridIndex_cube_le κ hκ hκ' n)
  rw [hx] at hb
  have hbR : (checkerboardEstimatorWork leX leY (xs n) (ys n) (powerGridIndex κ n+1) : ℝ) ≤
      6*((n : ℝ)+1)*(Nat.clog 2 (n+1) : ℝ)+320*((n : ℝ)+1) := by exact_mod_cast hb
  have hc := nat_clog_two_le_log (n+1) hn2
  simp only [Nat.cast_add,Nat.cast_one] at hc
  rw [show (2/Real.log 2)*Real.log ((n : ℝ)+1)=(2*Real.log ((n : ℝ)+1))/Real.log 2 by ring] at hc
  have hcm := (le_div_iff₀ h2).mp hc
  have hcN := mul_le_mul_of_nonneg_left hcm (show 0≤6*((n : ℝ)+1) by positivity)
  have hlN := mul_le_mul_of_nonneg_left hlog (show 0≤320*((n : ℝ)+1) by positivity)
  have hb2 := mul_le_mul_of_nonneg_right hbR h2.le
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) (h2.le.trans hlog))]
  rw [show (332/Real.log 2)*(((n : ℝ)+1)*Real.log ((n : ℝ)+1))=
    (332*(((n : ℝ)+1)*Real.log ((n : ℝ)+1)))/Real.log 2 by ring]
  apply (le_div_iff₀ h2).mpr
  nlinarith

end Verification
