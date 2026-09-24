import Verification.ArchimedeanCI
import Copula.Families.Joe

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

theorem joe_logBase_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => Real.log (1-Real.exp (-x))) (Real.exp (-t)/(1-Real.exp (-t))) t := by
  have hB : 0 < 1-Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have hh := ((((hasDerivAt_id t).neg).exp).const_sub 1).log hB.ne'
  convert hh using 1
  · rfl
  · dsimp; ring

theorem joe_logBase_deriv2 {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => Real.exp (-x)/(1-Real.exp (-x)))
      (-Real.exp (-t)/(1-Real.exp (-t))^2) t := by
  have hB : 0 < 1-Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have he := ((hasDerivAt_id t).neg).exp
  convert he.div (he.const_sub 1) hB.ne' using 1
  · rfl
  · dsimp; ring

theorem joe_logBase_concave : ConcaveOn ℝ (Ioi 0) (fun t => Real.log (1-Real.exp (-t))) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ioi 0)
  · intro t ht; exact (joe_logBase_deriv ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (joe_logBase_deriv (show 0 < t from interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact (joe_logBase_deriv2 (show 0 < t from interior_subset ht)).hasDerivWithinAt
  · intro t _
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) (sq_nonneg _)

noncomputable def joePsiDeriv (p t : ℝ) : ℝ := -p*Real.exp (-t)*(1-Real.exp (-t))^(p-1)

theorem joePsi_deriv {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => 1-(1-Real.exp (-x))^p) (joePsiDeriv p t) t := by
  have hB : 0 < 1-Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  have hh := ((((((hasDerivAt_id t).neg).exp).const_sub 1).rpow_const
    (p := p) (Or.inl hB.ne')).const_sub 1)
  convert hh using 1
  · rfl
  · dsimp [joePsiDeriv]; ring

theorem joePsiDeriv_neg {p t : ℝ} (hp : 0 < p) (ht : 0 < t) : joePsiDeriv p t < 0 := by
  have hB : 0 < 1-Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) (Real.exp_pos _))
    (Real.rpow_pos_of_pos hB _)

theorem joePsiDeriv_logconvex {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-joePsiDeriv p t)) := by
  have hc := ((joe_logBase_concave.neg.smul (sub_nonneg.mpr hp1)).add
    (concaveOn_id (convex_Ioi (0:ℝ))).neg).add_const (Real.log p)
  apply hc.congr
  intro t ht
  have ht0 : 0 < t := ht
  have hB : 0 < 1-Real.exp (-t) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht0))
  change (1-p)*(-Real.log (1-Real.exp (-t)))+(-t)+Real.log p = Real.log (-joePsiDeriv p t)
  have he : -joePsiDeriv p t = p*Real.exp (-t)*(1-Real.exp (-t))^(p-1) := by unfold joePsiDeriv; ring
  rw [he, Real.log_mul (mul_ne_zero hp.ne' (Real.exp_ne_zero _)) (Real.rpow_pos_of_pos hB _).ne',
    Real.log_mul hp.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_rpow hB]
  ring

theorem joe_isCI (θ : ℝ) (hθ : 1 ≤ θ) : (joe θ hθ).IsCI := by
  let φ : ℝ → ℝ := fun u => -Real.log (1-(1-u)^θ)
  let φ' : ℝ → ℝ := fun u => -(θ*(1-u)^(θ-1)/(1-(1-u)^θ))
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  have hbase (u : ℝ) (hu : u ∈ Ioo 0 1) : 0 < 1-(1-u)^θ ∧ 1-(1-u)^θ < 1 := by
    have h₁ := Real.rpow_lt_one (by linarith [hu.2] : 0 ≤ 1-u) (by linarith [hu.1] : 1-u < 1) hp
    have h₂ := Real.rpow_pos_of_pos (by linarith [hu.2] : 0 < 1-u) θ
    constructor <;> linarith
  apply generator_isCI_of_logconvex_neg_deriv (joeGenerator θ hθ) φ φ' (joePsiDeriv θ⁻¹)
  · intro u _ _; rfl
  · intro u hu
    exact neg_pos.mpr (Real.log_neg (hbase u hu).1 (hbase u hu).2)
  · intro u hu
    have hh := (((((hasDerivAt_id u).const_sub 1).rpow_const
      (p := θ) (Or.inl (by linarith [hu.2] : 1-u ≠ 0))).const_sub 1).log (hbase u hu).1.ne').neg
    convert hh using 1
    · rfl
    · dsimp [φ']; ring
  · intro t ht; exact joePsi_deriv ht
  · intro t ht; exact joePsiDeriv_neg (inv_pos.mpr hp) ht
  · exact joePsiDeriv_logconvex (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ)

end Verification
