import Verification.Nelsen19Limits
import Verification.Nelsen19Conditional
import Verification.SchurOrthantEquivalence
import Copula.Order.SymmetricSchur
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open ProbabilityTheory Set Filter Copula
open scoped unitInterval Topology

namespace Verification

theorem n19_exp_le {θ : ℝ} (hθ : 0 ≤ θ) {u : I} (hu : 0 < (u:ℝ)) :
    Real.exp θ ≤ Real.exp (θ/(u:ℝ)) := Real.exp_le_exp.mpr
  ((le_div_iff₀ hu).mpr (mul_le_of_le_one_right hθ u.property.2))

theorem n19_cdf_log_pos {θ : ℝ} (hθ : 0 < θ) {u v : I}
    (hu : 0 < (u:ℝ)) (hv : 0 < (v:ℝ)) :
    0 < Real.log (Real.exp (θ/(u:ℝ))+Real.exp (θ/(v:ℝ))-Real.exp θ) := by
  apply Real.log_pos
  have he := Real.one_lt_exp_iff.mpr hθ
  have h₁ := n19_exp_le hθ.le hu
  have h₂ := n19_exp_le hθ.le hv
  linarith

theorem nelsen19_lowerOrthant_monotone_pos {θ η : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hθη : θ ≤ η) :
    (nelsen19 θ hθ.le).LowerOrthantLE (nelsen19 η hη.le) := by
  intro x
  have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
  rw [hx, nelsen19_cdf hθ, nelsen19_cdf hη]
  split_ifs with hz
  · rfl
  have hu : 0 < (x 0:ℝ) := lt_of_le_of_ne (x 0).property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr (not_or.mp hz).1))
  have hv : 0 < (x 1:ℝ) := lt_of_le_of_ne (x 1).property.1 (Ne.symm (unitInterval.coe_ne_zero.mpr (not_or.mp hz).2))
  have hr : 1 ≤ η/θ := (le_div_iff₀ hθ).mpr (by simpa using hθη)
  have hh := BivariateGenerator.convex_increment (convexOn_rpow hr)
    (Real.exp_pos θ).le (show (0:ℝ) ≤ 0 from le_rfl)
    (n19_exp_le hθ.le hu) (sub_nonneg.mpr (n19_exp_le hθ.le hv))
  have he (u : ℝ) : (Real.exp (θ/u))^(η/θ) = Real.exp (η/u) := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have he0 : (Real.exp θ)^(η/θ) = Real.exp η := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hadd : Real.exp θ+(Real.exp (θ/(x 1:ℝ))-Real.exp θ) = Real.exp (θ/(x 1:ℝ)) := by ring
  simp only [hadd, add_zero, he, he0] at hh
  have hbase : 0 < Real.exp (η/(x 0:ℝ))+Real.exp (η/(x 1:ℝ))-Real.exp η := by
    have h₁ := n19_exp_le hη.le hu
    linarith [Real.exp_pos (η/(x 1:ℝ))]
  have hpow : Real.exp (η/(x 0:ℝ))+Real.exp (η/(x 1:ℝ))-Real.exp η ≤
      (Real.exp (θ/(x 0:ℝ))+Real.exp (θ/(x 1:ℝ))-Real.exp θ)^(η/θ) := by
    rw [← add_sub_assoc] at hh
    linarith
  have hl := Real.log_le_log hbase hpow
  have hbaseθ : 0 < Real.exp (θ/(x 0:ℝ))+Real.exp (θ/(x 1:ℝ))-Real.exp θ := by
    have h₁ := n19_exp_le hθ.le hu
    linarith [Real.exp_pos (θ/(x 1:ℝ))]
  rw [Real.log_rpow hbaseθ] at hl
  have hlθ := n19_cdf_log_pos hθ hu hv
  have hlη := n19_cdf_log_pos hη hu hv
  apply (div_le_div_iff₀ hlθ hlη).mpr
  have hm := mul_le_mul_of_nonneg_left hl hθ.le
  field_simp at hm
  nlinarith

theorem nelsen19_lowerOrthant_monotone {θ η : ℝ}
    (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (nelsen19 θ hθ).LowerOrthantLE (nelsen19 η hη) := by
  by_cases hz : θ = 0
  · subst θ
    by_cases he : η = 0
    · subst η; exact fun _ => le_rfl
    have hp : 0 < η := lt_of_le_of_ne hη (Ne.symm he)
    let p : ℕ → ℝ := fun n => η/((n:ℝ)+1)
    have hp' (n : ℕ) : 0 < p n := div_pos hp (by positivity)
    have ht : Tendsto p atTop (𝓝 0) := by
      simpa [p, div_eq_mul_inv] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul η
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, nelsen19_zero]
    apply le_of_tendsto (nelsen19_tendsto_zero p (fun n => (hp' n).le) ht (x 0) (x 1))
    apply Eventually.of_forall
    intro n
    apply nelsen19_lowerOrthant_monotone_pos (hp' n) hp _
    exact (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  · exact nelsen19_lowerOrthant_monotone_pos (lt_of_le_of_ne hθ (Ne.symm hz))
      (lt_of_lt_of_le (lt_of_le_of_ne hθ (Ne.symm hz)) hθη) hθη

theorem nelsen19_schur_monotone {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hθη : θ ≤ η) :
    (nelsen19 θ hθ).SchurBothLE (nelsen19 η hη) := by
  have ho := nelsen19_lowerOrthant_monotone hθ hη hθη
  constructor
  · exact (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen19_isCI θ hθ).1 (nelsen19_isCI η hη).1).mpr ho
  · apply (schurLE_iff_lowerOrthantLE_isSI _ _ (nelsen19_isCI θ hθ).2 (nelsen19_isCI η hη).2).mpr
    intro x
    have hx : x = ![x 0,x 1] := by ext i; fin_cases i <;> rfl
    rw [hx, cdf_transpose, cdf_transpose]
    exact ho ![x 1,x 0]

end Verification
