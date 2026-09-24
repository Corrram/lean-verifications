import Verification.Nelsen17
import Verification.ArchimedeanCD

open ProbabilityTheory Set Copula
open scoped unitInterval

namespace Verification

noncomputable def n17LogDeriv (a t : ℝ) : ℝ := -t+(a⁻¹-1)*Real.log (n17Base a t)
noncomputable def n17LogDerivPrime (a t : ℝ) : ℝ := -1-(a⁻¹-1)*n17A a*Real.exp (-t)/n17Base a t

theorem n17LogDeriv_deriv {a t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (n17LogDeriv a) (n17LogDerivPrime a t) t := by
  have hh := (hasDerivAt_id t).neg.add
    (((n17Base_deriv a t).log (n17Base_pos ht).ne').const_mul (a⁻¹-1))
  convert hh using 1
  · rfl
  · dsimp [n17LogDerivPrime]; ring

theorem n17LogDeriv_deriv2 {a t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (n17LogDerivPrime a) ((a⁻¹-1)*n17A a*Real.exp (-t)/(n17Base a t)^2) t := by
  have hh := (((((hasDerivAt_id t).neg.exp).const_mul ((a⁻¹-1)*n17A a)).div
    (n17Base_deriv a t) (n17Base_pos ht).ne').const_sub (-1))
  convert hh using 1
  · rfl
  · dsimp only [Pi.neg_apply, id_eq]
    field_simp
    dsimp [n17Base]
    ring

theorem n17PsiDeriv_logconvex {a : ℝ} (ha : a ≠ 0) (ha1 : a ≤ 1) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-n17PsiDeriv a t)) := by
  have hcoeff : 0 ≤ (a⁻¹-1)*n17A a := by
    have hh := mul_nonneg (n17_coeff_pos ha).le (sub_nonneg.mpr ha1)
    have he : a⁻¹*n17A a*(1-a) = (a⁻¹-1)*n17A a := by field_simp
    rwa [he] at hh
  have hc : ConvexOn ℝ (Ioi 0) (n17LogDeriv a) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
    · intro t ht; exact (n17LogDeriv_deriv ht.le).continuousAt.continuousWithinAt
    · intro t ht; exact (n17LogDeriv_deriv (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact (n17LogDeriv_deriv2 (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t _; exact div_nonneg (mul_nonneg hcoeff (Real.exp_pos _).le) (sq_nonneg _)
  apply (hc.add_const (Real.log (a⁻¹*n17A a))).congr
  intro t ht
  have hb := n17Base_pos (a := a) ht.le
  have he : -n17PsiDeriv a t = (a⁻¹*n17A a)*Real.exp (-t)*n17Base a t^(a⁻¹-1) := by
    dsimp [n17PsiDeriv]; ring
  change n17LogDeriv a t + Real.log (a⁻¹*n17A a) = Real.log (-n17PsiDeriv a t)
  rw [he, Real.log_mul (mul_ne_zero (n17_coeff_pos ha).ne' (Real.exp_ne_zero _)) (Real.rpow_pos_of_pos hb _).ne',
    Real.log_mul (n17_coeff_pos ha).ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_rpow hb]
  dsimp [n17LogDeriv]
  ring

theorem n17Ratio_lt_one {a u : ℝ} (ha : a ≠ 0) (hu : u ∈ Ioo 0 1) : n17Ratio a u < 1 := by
  have hu0 := hu.1
  have hu1 := hu.2
  rcases lt_or_gt_of_ne ha with hn | hp
  · apply (div_lt_one_of_neg (n17A_neg hn)).mpr
    exact sub_lt_sub_right (Real.rpow_lt_rpow_of_neg (by linarith : 0 < 1+u)
      (by linarith : 1+u < 2) hn) 1
  · apply (div_lt_one (n17A_pos hp)).mpr
    exact sub_lt_sub_right (Real.rpow_lt_rpow (by linarith : 0 ≤ 1+u) (by linarith : 1+u < 2) hp) 1

theorem n17Inv_deriv {a u : ℝ} (ha : a ≠ 0) (hu : 0 < u) :
    HasDerivAt (fun x => -Real.log (n17Ratio a x))
      (-a*(1+u)^(a-1)/((1+u)^a-1)) u := by
  have hR := n17Ratio_pos ha hu
  have hn : (1+u)^a-1 ≠ 0 := (div_ne_zero_iff.mp hR.ne').1
  have hd := (((((hasDerivAt_id u).const_add 1).rpow_const (p := a)
    (Or.inl (by linarith : 1+u ≠ 0))).sub_const 1).div_const (n17A a)).log hR.ne' |>.neg
  convert hd using 1
  · rfl
  · dsimp [n17Ratio]
    field_simp [n17A_ne ha]

theorem nelsen17_isCI (θ : ℝ) (hθ : θ ≠ 0) (hθ1 : -1 ≤ θ) : (nelsen17 θ hθ).IsCI := by
  have ha : -θ ≠ 0 := neg_ne_zero.mpr hθ
  let φ : ℝ → ℝ := fun u => -Real.log (n17Ratio (-θ) u)
  let φ' : ℝ → ℝ := fun u => -(-θ)*(1+u)^(-θ-1)/((1+u)^(-θ)-1)
  apply generator_isCI_of_logconvex_neg_deriv (n17Generator (-θ) ha) φ φ' (n17PsiDeriv (-θ))
  · intro u _ _; rfl
  · intro u hu
    exact neg_pos.mpr (Real.log_neg (n17Ratio_pos ha hu.1) (n17Ratio_lt_one ha hu))
  · intro u hu; exact n17Inv_deriv ha hu.1
  · intro t ht; exact n17Psi_deriv ht.le
  · intro t ht; exact n17PsiDeriv_neg ha ht.le
  · exact n17PsiDeriv_logconvex ha (by linarith)

theorem n17PsiDeriv_logconcave {a : ℝ} (ha : a ≠ 0) (ha1 : 1 ≤ a) :
    ConcaveOn ℝ (Ioi 0) (fun t => Real.log (-n17PsiDeriv a t)) := by
  have hcoeff : (a⁻¹-1)*n17A a ≤ 0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (n17_coeff_pos ha).le (sub_nonpos.mpr ha1)
    have he : a⁻¹*n17A a*(1-a) = (a⁻¹-1)*n17A a := by field_simp
    rwa [he] at hh
  have hc : ConcaveOn ℝ (Ioi 0) (n17LogDeriv a) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
    · intro t ht; exact (n17LogDeriv_deriv ht.le).continuousAt.continuousWithinAt
    · intro t ht; exact (n17LogDeriv_deriv (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t ht; exact (n17LogDeriv_deriv2 (le_of_lt (interior_subset ht))).hasDerivWithinAt
    · intro t _; exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hcoeff (Real.exp_pos _).le) (sq_nonneg _)
  apply (hc.add_const (Real.log (a⁻¹*n17A a))).congr
  intro t ht
  have hb := n17Base_pos (a := a) ht.le
  have he : -n17PsiDeriv a t = (a⁻¹*n17A a)*Real.exp (-t)*n17Base a t^(a⁻¹-1) := by
    dsimp [n17PsiDeriv]; ring
  change n17LogDeriv a t + Real.log (a⁻¹*n17A a) = Real.log (-n17PsiDeriv a t)
  rw [he, Real.log_mul (mul_ne_zero (n17_coeff_pos ha).ne' (Real.exp_ne_zero _)) (Real.rpow_pos_of_pos hb _).ne',
    Real.log_mul (n17_coeff_pos ha).ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_rpow hb]
  dsimp [n17LogDeriv]
  ring

theorem nelsen17_isCD (θ : ℝ) (hθ : θ ≠ 0) (hθ1 : θ ≤ -1) : (nelsen17 θ hθ).IsCD := by
  have ha : -θ ≠ 0 := neg_ne_zero.mpr hθ
  let φ : ℝ → ℝ := fun u => -Real.log (n17Ratio (-θ) u)
  let φ' : ℝ → ℝ := fun u => -(-θ)*(1+u)^(-θ-1)/((1+u)^(-θ)-1)
  apply generator_isCD_of_logconcave_neg_deriv (n17Generator (-θ) ha) φ φ' (n17PsiDeriv (-θ))
  · intro u _ _; rfl
  · intro u hu
    exact neg_pos.mpr (Real.log_neg (n17Ratio_pos ha hu.1) (n17Ratio_lt_one ha hu))
  · intro u hu; exact n17Inv_deriv ha hu.1
  · intro t ht; exact n17Psi_deriv ht.le
  · intro t ht; exact n17PsiDeriv_neg ha ht.le
  · exact n17PsiDeriv_logconcave ha (by linarith)

end Verification
