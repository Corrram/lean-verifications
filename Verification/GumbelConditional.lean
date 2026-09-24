import Verification.ArchimedeanCI
import Verification.SchurOrthantEquivalence
import Copula.Dependence.Gumbel
import Copula.Order.SymmetricSchur
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

open ProbabilityTheory Set
open Copula
open scoped unitInterval

namespace Verification

noncomputable def gumbelPsiDeriv (p t : ℝ) : ℝ := -p*t^(p-1)*Real.exp (-t^p)

theorem gumbelPsi_deriv {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => Real.exp (-x^p)) (gumbelPsiDeriv p t) t := by
  have hh := (((hasDerivAt_id t).rpow_const (p := p) (Or.inl ht.ne')).neg).exp
  convert hh using 1
  · rfl
  · dsimp [gumbelPsiDeriv]
    ring

theorem gumbelPsiDeriv_neg {p t : ℝ} (hp : 0 < p) (ht : 0 < t) : gumbelPsiDeriv p t < 0 := by
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos hp) (Real.rpow_pos_of_pos ht _)) (Real.exp_pos _)

theorem gumbelPsiDeriv_logconvex {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ConvexOn ℝ (Ioi 0) (fun t => Real.log (-gumbelPsiDeriv p t)) := by
  have h₁ := strictConcaveOn_log_Ioi.concaveOn.neg.smul (sub_nonneg.mpr hp1)
  have h₂ := ((Real.concaveOn_rpow hp.le hp1).neg).subset Ioi_subset_Ici_self (convex_Ioi 0)
  have hc := (h₁.add h₂).add_const (Real.log p)
  apply hc.congr
  intro t ht
  have ht0 : 0 < t := ht
  change (1-p)*(-Real.log t)+(-t^p)+Real.log p = Real.log (-gumbelPsiDeriv p t)
  have he : -gumbelPsiDeriv p t = p*t^(p-1)*Real.exp (-t^p) := by unfold gumbelPsiDeriv; ring
  rw [he, Real.log_mul (mul_ne_zero hp.ne' (Real.rpow_pos_of_pos ht0 _).ne') (Real.exp_ne_zero _),
    Real.log_mul hp.ne' (Real.rpow_pos_of_pos ht0 _).ne', Real.log_rpow ht0, Real.log_exp]
  ring

theorem gumbel_isCI (θ : ℝ) (hθ : 1 ≤ θ) : (gumbel θ hθ).IsCI := by
  let φ : ℝ → ℝ := fun u => (-Real.log u)^θ
  let φ' : ℝ → ℝ := fun u => -u⁻¹*θ*(-Real.log u)^(θ-1)
  have hp : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
  apply generator_isCI_of_logconvex_neg_deriv (gumbelGenerator θ hθ) φ φ' (gumbelPsiDeriv θ⁻¹)
  · intro u _ _; rfl
  · intro u hu
    exact Real.rpow_pos_of_pos (neg_pos.mpr (Real.log_neg hu.1 hu.2)) _
  · intro u hu
    exact ((Real.hasDerivAt_log hu.1.ne').neg).rpow_const
      (Or.inl (neg_pos.mpr (Real.log_neg hu.1 hu.2)).ne')
  · intro t ht
    exact gumbelPsi_deriv ht
  · intro t ht
    exact gumbelPsiDeriv_neg (inv_pos.mpr hp) ht
  · exact gumbelPsiDeriv_logconvex (inv_pos.mpr hp) (inv_le_one_of_one_le₀ hθ)

theorem gumbel_schur_monotone {θ η : ℝ} (hθ : 1 ≤ θ) (hη : 1 ≤ η) (hθη : θ ≤ η) :
    (gumbel θ hθ).SchurBothLE (gumbel η hη) := by
  have ho := lowerOrthantLE_gumbel hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (gumbel_isCI θ hθ).1
      (gumbel_isCI η hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (gumbel_isCI θ hθ).2
      (gumbel_isCI η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
