import Verification.Nelsen17
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n17Comparison (a b t : ℝ) : ℝ :=
  -Real.log ((n17Base a t^(b/a)-1)/n17A b)
noncomputable def n17ComparisonPrime (a b t : ℝ) : ℝ :=
  (b/a)*n17A a*Real.exp (-t)*n17Base a t^(b/a-1)/(n17Base a t^(b/a)-1)

theorem n17Comparison_denom {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : 0 ≤ t) :
    n17Base a t^(b/a)-1 ≠ 0 := by
  have hB := n17Base_pos (a := a) ht
  have hr := div_ne_zero hb ha
  intro he
  have he1 : n17Base a t^(b/a) = 1 := by linarith
  have hh := congrArg (fun x : ℝ => x^((b/a)⁻¹)) he1
  rw [Real.rpow_rpow_inv hB.le hr, Real.one_rpow] at hh
  have hn := mul_ne_zero (n17A_ne ha) (Real.exp_ne_zero (-t))
  apply hn
  dsimp [n17Base] at hh
  linarith

theorem n17Comparison_deriv {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : 0 ≤ t) :
    HasDerivAt (n17Comparison a b) (n17ComparisonPrime a b t) t := by
  have hn := n17Comparison_denom ha hb ht
  have hh := (((((n17Base_deriv a t).rpow_const (p := b/a) (Or.inl (n17Base_pos ht).ne')).sub_const 1).div_const (n17A b)).log
    (div_ne_zero hn (n17A_ne hb))).neg
  convert hh using 1
  · rfl
  · dsimp [n17ComparisonPrime]
    field_simp [n17A_ne hb]

theorem n17Comparison_deriv2 {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : 0 ≤ t) :
    HasDerivAt (n17ComparisonPrime a b)
      ((b/a)*n17A a*Real.exp (-t)*n17Base a t^(b/a-2)*
        (1+(b/a)*n17A a*Real.exp (-t)-n17Base a t^(b/a))/(n17Base a t^(b/a)-1)^2) t := by
  have hB := n17Base_pos (a := a) ht
  have hP := (n17Base_deriv a t).rpow_const (p := b/a) (Or.inl hB.ne')
  have hh := (((((hasDerivAt_id t).neg.exp).const_mul ((b/a)*n17A a)).mul
    ((n17Base_deriv a t).rpow_const (p := b/a-1) (Or.inl hB.ne'))).div
      (hP.sub_const 1) (n17Comparison_denom ha hb ht))
  have he : n17Base a t^(b/a-1) = n17Base a t^(b/a-2)*n17Base a t := by
    rw [show b/a-1 = (b/a-2)+1 by ring, Real.rpow_add_one hB.ne']
  have he2 : n17Base a t^(b/a) = n17Base a t^(b/a-2)*(n17Base a t)^2 := by
    calc
      _ = n17Base a t^((b/a-2)+2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hB, Real.rpow_two]
  convert hh using 1
  · rfl
  · dsimp only [Pi.neg_apply,Pi.mul_apply,id_eq]
    apply congrArg (fun x : ℝ => x/(n17Base a t^(b/a)-1)^2)
    rw [show b/a-1-1 = b/a-2 by ring, he, he2]
    dsimp [n17Base]
    ring

theorem n17_bernoulli_nonpos {r q : ℝ} (hr : r ≤ 0) (hq : 0 < 1+q) :
    1+r*q ≤ (1+q)^r := by
  have hl := Real.log_le_sub_one_of_pos hq
  have hm := mul_le_mul_of_nonpos_left hl hr
  have he := Real.add_one_le_exp (r*Real.log (1+q))
  rw [Real.rpow_def_of_pos hq, mul_comm (Real.log (1+q)) r]
  nlinarith

theorem n17Comparison_convex {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hba : b ≤ a) :
    ConvexOn ℝ (Ici 0) (n17Comparison a b) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 0)
  · intro t ht; exact (n17Comparison_deriv ha hb ht).continuousAt.continuousWithinAt
  · intro t ht; exact (n17Comparison_deriv ha hb (interior_subset ht)).hasDerivWithinAt
  · intro t ht; exact (n17Comparison_deriv2 ha hb (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    have hB := n17Base_pos (a := a) (interior_subset ht)
    have he := (Real.exp_pos (-t)).le
    have hpow := (Real.rpow_pos_of_pos hB (b/a-2)).le
    have hq : -1 ≤ n17A a*Real.exp (-t) := by dsimp [n17Base] at hB; linarith
    apply div_nonneg _ (sq_nonneg _)
    rcases lt_or_gt_of_ne ha with han | hap
    · have hr : 1 ≤ b/a := (le_div_iff_of_neg han).mpr (by simpa using hba)
      have hh := one_add_mul_self_le_rpow_one_add hq hr
      change 1+(b/a)*(n17A a*Real.exp (-t)) ≤ n17Base a t^(b/a) at hh
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (by linarith) (n17A_neg han).le) he) hpow) (by nlinarith)
    · by_cases hbp : 0 ≤ b
      · have hr0 := div_nonneg hbp hap.le
        have hr1 : b/a ≤ 1 := (div_le_one hap).mpr hba
        have hh := rpow_one_add_le_one_add_mul_self hq hr0 hr1
        change n17Base a t^(b/a) ≤ 1+(b/a)*(n17A a*Real.exp (-t)) at hh
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hr0 (n17A_pos hap).le) he) hpow) (by nlinarith)
      · have hr := div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hbp) hap.le
        have hh := n17_bernoulli_nonpos hr hB
        change 1+(b/a)*(n17A a*Real.exp (-t)) ≤ n17Base a t^(b/a) at hh
        exact mul_nonneg_of_nonpos_of_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg hr (n17A_pos hap).le) he) hpow) (by nlinarith)

theorem n17Comparison_zero {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : n17Comparison a b 0 = 0 := by
  have he : n17Base a 0 = (2:ℝ)^a := by simp [n17Base,n17A]
  unfold n17Comparison
  rw [he, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), show a*(b/a) = b by field_simp]
  change -Real.log (n17A b/n17A b) = 0
  rw [div_self (n17A_ne hb), Real.log_one, neg_zero]

theorem n17Comparison_superadd {a b s t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hba : b ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    n17Comparison a b s+n17Comparison a b t ≤ n17Comparison a b (s+t) := by
  have hh := BivariateGenerator.convex_increment (n17Comparison_convex ha hb hba)
    (show (0:ℝ) ≤ 0 from le_rfl) (show (0:ℝ) ≤ 0 from le_rfl) hs ht
  simp only [zero_add, add_zero, n17Comparison_zero ha hb] at hh
  linarith

theorem n17Comparison_inv {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (u : I) (hu : u ≠ 0) :
    n17Comparison a b ((n17Generator a ha).invFun u) = (n17Generator b hb).invFun u := by
  have hu0 : 0 < (u:ℝ) := lt_of_le_of_ne u.property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr hu))
  have hr := n17Ratio_pos ha hu0
  have he : n17Base a (-Real.log (n17Ratio a u)) = (1+(u:ℝ))^a := by
    unfold n17Base
    rw [neg_neg,Real.exp_log hr]
    dsimp [n17Ratio]
    field_simp [n17A_ne ha]
    ring
  change -Real.log ((n17Base a (-Real.log (n17Ratio a u))^(b/a)-1)/n17A b) = _
  rw [he, ← Real.rpow_mul (by linarith : 0 ≤ 1+(u:ℝ)), show a*(b/a) = b by field_simp]
  rfl

theorem n17Psi_pos {a t : ℝ} (ha : a ≠ 0) (ht : 0 ≤ t) : 0 < n17Psi a t := by
  apply sub_pos.mpr
  rcases lt_or_gt_of_ne ha with hn | hp
  · have hlt : n17Base a t < 1 := by
      have hh := mul_neg_of_neg_of_pos (n17A_neg hn) (Real.exp_pos (-t))
      dsimp [n17Base]; linarith
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg (n17Base_pos ht) hlt (inv_neg''.mpr hn)
  · have hlt : 1 < n17Base a t := by
      have hh := mul_pos (n17A_pos hp) (Real.exp_pos (-t))
      dsimp [n17Base]; linarith
    exact Real.one_lt_rpow hlt (inv_pos.mpr hp)

theorem n17Comparison_psi {a b t : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (ht : 0 ≤ t) :
    n17Psi b (n17Comparison a b t) = n17Psi a t := by
  have hB := n17Base_pos (a := a) ht
  have he : n17Ratio b (n17Psi a t) = (n17Base a t^(b/a)-1)/n17A b := by
    dsimp [n17Ratio,n17Psi]
    rw [show 1+(n17Base a t^a⁻¹-1) = n17Base a t^a⁻¹ by ring,
      ← Real.rpow_mul hB.le, show a⁻¹*b = b/a by ring]
  have hr := n17Ratio_pos hb (n17Psi_pos ha ht)
  rw [he] at hr
  unfold n17Psi n17Base n17Comparison
  rw [neg_neg, Real.exp_log hr]
  have hbase : 1+n17A b*((n17Base a t^(b/a)-1)/n17A b) = n17Base a t^(b/a) := by
    field_simp [n17A_ne hb]; ring
  change (1+n17A b*((n17Base a t^(b/a)-1)/n17A b))^b⁻¹-1 = _
  rw [hbase, ← Real.rpow_mul hB.le, show (b/a)*b⁻¹ = a⁻¹ by field_simp]
  rfl

end Verification
