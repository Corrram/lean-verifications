import Verification.ExclusionBand

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace Verification

/-- The source's piecewise lower edge, with its natural alpha=1/2 extension. -/
noncomputable def diagonalHoleLower (α β : ℝ) (u : I) : ℝ :=
  if (u : ℝ) ≤ α then 0 else if 1-α ≤ (u : ℝ) then 1-β
  else (1-β)/(1-2*α)*((u : ℝ)-α)

theorem diagonalHoleLower_measurable (α β : ℝ) : Measurable (diagonalHoleLower α β) := by
  unfold diagonalHoleLower
  exact Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const (by fun_prop))

theorem diagonalHoleLower_mem (α β : ℝ) (_hα : α ∈ Icc 0 (1/2)) (hβ : β ∈ Icc 0 (1/2)) (u : I) :
    diagonalHoleLower α β u ∈ Icc 0 (1-β) := by
  have hb : 0 ≤ 1-β := by linarith [hβ.2]
  unfold diagonalHoleLower
  split_ifs with h1 h2
  · exact ⟨le_rfl,hb⟩
  · exact ⟨hb,le_rfl⟩
  · have hd : 0 < 1-2*α := by linarith
    have hu : 0 ≤ (u : ℝ)-α := by linarith
    constructor
    · exact mul_nonneg (div_nonneg hb hd.le) hu
    · rw [div_mul_eq_mul_div,div_le_iff₀ hd]
      exact mul_le_mul_of_nonneg_left (by linarith) hb

noncomputable def diagonalHoleBand (α β : ℝ) (hα : α ∈ Icc 0 (1/2)) (hβ : β ∈ Icc 0 (1/2)) : ExclusionBand where
  width := β
  width_nonneg := hβ.1
  width_lt_one := by linarith [hβ.2]
  lower := diagonalHoleLower α β
  lower_measurable := diagonalHoleLower_measurable α β
  lower_nonneg u := (diagonalHoleLower_mem α β hα hβ u).1
  lower_le u := (diagonalHoleLower_mem α β hα hβ u).2

/-- Rank standardization of the joint uniform density outside the diagonal hole. -/
noncomputable def diagonalHoleCopula (α β : ℝ) (hα : α ∈ Icc 0 (1/2)) (hβ : β ∈ Icc 0 (1/2)) : Copula 2 :=
  (diagonalHoleBand α β hα hβ).copula

/-- The finite-mu path in Equation (33). -/
noncomputable def diagonalHoleAlpha (μ : ℝ) : ℝ := if μ ≤ 2 then 3/20*μ else 1/2-2/(5*μ)
noncomputable def diagonalHoleBeta (μ : ℝ) : ℝ := 1/4*min μ 2

theorem diagonalHolePath_mem (μ : ℝ) (hμ : 0 ≤ μ) :
    diagonalHoleAlpha μ ∈ Icc 0 (1/2) ∧ diagonalHoleBeta μ ∈ Icc 0 (1/2) := by
  unfold diagonalHoleAlpha diagonalHoleBeta
  by_cases hm : μ ≤ 2
  · rw [ite_eq_left hm,min_eq_left hm]
    constructor <;> constructor <;> linarith
  · rw [ite_eq_right hm,min_eq_right (le_of_not_ge hm)]
    have hp : 0 < μ := by linarith
    have hd : 0 < 5*μ := by positivity
    have hb : 2/(5*μ) ≤ 1/2 := (div_le_iff₀ hd).mpr (by linarith)
    have hn : 0 ≤ 2/(5*μ) := by positivity
    constructor <;> constructor <;> linarith

end Verification
