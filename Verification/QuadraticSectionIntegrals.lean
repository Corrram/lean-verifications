import Verification.QuadraticBand
import Verification.RampIntegrals

/-! # Exact section moments for clamped quadratics -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

noncomputable def quadraticLower (q : ℝ) : ℝ := Real.sqrt (max 0 q)
noncomputable def quadraticUpper (b q : ℝ) : ℝ := min 1 (Real.sqrt (q+1/b))

theorem quadratic_switch_bounds (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1) :
    0 ≤ quadraticLower q ∧ quadraticLower q ≤ quadraticUpper b q ∧ quadraticUpper b q ≤ 1 := by
  have hR : 0 ≤ q+1/b := by linarith [show -(1/b) ≤ q by simpa only [neg_div] using hq.1]
  have hinv : 0 ≤ 1/b := by positivity
  refine ⟨Real.sqrt_nonneg _,?_,min_le_left _ _⟩
  apply le_min
  · exact Real.sqrt_le_one.mpr (max_le zero_le_one hq.2)
  · exact Real.sqrt_le_sqrt (max_le hR (by linarith))

theorem quadratic_section_moment (b q : ℝ) (hb : 0 < b) (hq : q ∈ Icc (-1/b) 1)
    (m k : ℕ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..1,x^m*unitClamp (b*(x^2-q))^k)=
      b^k*(∫ x in quadraticLower q..quadraticUpper b q,x^m*(x^2-q)^k)+
      ∫ x in quadraticUpper b q..1,x^m := by
  let r := quadraticLower q
  let s := quadraticUpper b q
  obtain ⟨hr,hrs,hs⟩ := quadratic_switch_bounds b q hb hq
  change 0 ≤ r at hr
  change r ≤ s at hrs
  change s ≤ 1 at hs
  have hqR : 0 ≤ q+1/b := by linarith [show -(1/b) ≤ q by simpa only [neg_div] using hq.1]
  have hrsq : r^2=max 0 q := Real.sq_sqrt (le_max_left _ _)
  have hRsq := Real.sq_sqrt hqR
  have hf : Continuous (fun x : ℝ => x^m*unitClamp (b*(x^2-q))^k) := by unfold unitClamp; fun_prop
  have hlo (x : ℝ) (hx : x ∈ Ioo 0 r) : unitClamp (b*(x^2-q))=0 := by
    have hq0 : 0 < q := by
      by_contra hh
      have he : max 0 q=0 := max_eq_left (le_of_not_gt hh)
      rw [he] at hrsq
      nlinarith [hx.1,hx.2]
    rw [max_eq_right hq0.le] at hrsq
    unfold unitClamp
    rw [max_eq_left (mul_nonpos_of_nonneg_of_nonpos hb.le (by nlinarith [hx.1,hx.2]))]
    norm_num
  have hmid (x : ℝ) (hx : x ∈ Ioo r s) : unitClamp (b*(x^2-q))=b*(x^2-q) := by
    have hx0 : 0 ≤ x := hr.trans hx.1.le
    have hxR : x ≤ Real.sqrt (q+1/b) := hx.2.le.trans (min_le_right _ _)
    have ht0 : 0 ≤ b*(x^2-q) := mul_nonneg hb.le (by nlinarith [le_max_right (0 : ℝ) q,hx.1])
    have hinv : b*(1/b)=1 := by field_simp
    have ht1 : b*(x^2-q) ≤ 1 := by
      have hh : x^2-q ≤ 1/b := by nlinarith [Real.sqrt_nonneg (q+1/b)]
      nlinarith [mul_le_mul_of_nonneg_left hh hb.le]
    unfold unitClamp
    rw [max_eq_right ht0,min_eq_right ht1]
  have hhi (x : ℝ) (hx : x ∈ Ioo s 1) : unitClamp (b*(x^2-q))=1 := by
    have hs1 : s < 1 := hx.1.trans hx.2
    have hR1 : Real.sqrt (q+1/b) < 1 := by
      by_contra hh
      have he : s=1 := min_eq_left (le_of_not_gt hh)
      linarith
    have hes : s=Real.sqrt (q+1/b) := min_eq_right hR1.le
    have hx0 : 0 ≤ x := hr.trans (hrs.trans hx.1.le)
    have ht : 1 ≤ b*(x^2-q) := by
      have hh : 1/b ≤ x^2-q := by rw [hes] at hx; nlinarith [Real.sqrt_nonneg (q+1/b),hx.1]
      have hinv : b*(1/b)=1 := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hh hb.le]
    unfold unitClamp
    rw [max_eq_right (by linarith),min_eq_left ht]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 r) (hf.intervalIntegrable r 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable r s) (hf.intervalIntegrable s 1)]
  have hzero : (∫ x in (0 : ℝ)..r,x^m*unitClamp (b*(x^2-q))^k)=0 := by
    calc
      _ = ∫ x in (0 : ℝ)..r,(0 : ℝ) := intervalIntegral.integral_congr_Ioo_of_le hr (by
        intro x hx; dsimp only; rw [hlo x hx,zero_pow hk,mul_zero])
      _ = 0 := by simp
  rw [hzero,zero_add]
  congr 1
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hrs
    intro x hx
    dsimp only
    rw [hmid x hx,mul_pow]
    ring
  · apply intervalIntegral.integral_congr_Ioo_of_le hs
    intro x hx
    dsimp only
    rw [hhi x hx,one_pow,mul_one]

noncomputable def quadraticT (q x : ℝ) : ℝ := x^3/3-q*x
noncomputable def quadraticF (q x : ℝ) : ℝ := x^5/5-(2*q/3)*x^3+q^2*x
noncomputable def quadraticS (q x : ℝ) : ℝ := x^5/5-(q/3)*x^3

theorem integral_quadratic_polynomials (q a c : ℝ) :
    (∫ x in a..c,x^2-q)=quadraticT q c-quadraticT q a ∧
    (∫ x in a..c,(x^2-q)^2)=quadraticF q c-quadraticF q a ∧
    (∫ x in a..c,x^2*(x^2-q))=quadraticS q c-quadraticS q a := by
  have ht (x : ℝ) : HasDerivAt (quadraticT q) (x^2-q) x := by
    convert! (((hasDerivAt_id x).pow 3).div_const 3).sub ((hasDerivAt_id x).const_mul q) using 1
    simp only [id_eq,Nat.cast_ofNat]; ring
  have hf (x : ℝ) : HasDerivAt (quadraticF q) ((x^2-q)^2) x := by
    convert! ((((hasDerivAt_id x).pow 5).div_const 5).sub
      (((hasDerivAt_id x).pow 3).const_mul (2*q/3))).add ((hasDerivAt_id x).const_mul (q^2)) using 1
    simp only [id_eq,Nat.cast_ofNat]; ring
  have hs (x : ℝ) : HasDerivAt (quadraticS q) (x^2*(x^2-q)) x := by
    convert! (((hasDerivAt_id x).pow 5).div_const 5).sub
      (((hasDerivAt_id x).pow 3).const_mul (q/3)) using 1
    simp only [id_eq,Nat.cast_ofNat]; ring
  exact ⟨intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => ht x) ((by fun_prop : Continuous (fun x : ℝ => x^2-q)).intervalIntegrable a c),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hf x) ((by fun_prop : Continuous (fun x : ℝ => (x^2-q)^2)).intervalIntegrable a c),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hs x) ((by fun_prop : Continuous (fun x : ℝ => x^2*(x^2-q))).intervalIntegrable a c)⟩

end Verification
