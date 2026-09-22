import Verification.DiagonalHoleEndpoints
import Papers.Rockel2026XiFootrule.LowerEndpoint

/-! # The two-parameter family in Section 3.2

The displayed density is identified with an actual copula law. The proof uses
probability-integral transforms and almost-everywhere quantile inversion, so
zero marginal densities and the closed-square parameter endpoints are covered.
-/

open MeasureTheory ProbabilityTheory Set Verification
open scoped unitInterval

namespace Papers.Rockel2026XiFootrule

noncomputable def twoParameter (α β : ℝ) (hα : α ∈ Icc 0 (1/2)) (hβ : β ∈ Icc 0 (1/2)) : Copula 2 :=
  diagonalHoleCopula α β hα hβ

/-- The pre-standardization law has the claimed two marginal distributions. -/
theorem twoParameter_raw_marginals (α β : ℝ) (hα : α ∈ Icc 0 (1/2)) (hβ : β ∈ Icc 0 (1/2)) :
    let B := diagonalHoleBand α β hα hβ
    B.measure.map Prod.fst=volume ∧
    B.measure.map Prod.snd=(volume : Measure I).withDensity (fun t => ENNReal.ofReal (B.columnDensity t)) :=
  ⟨ExclusionBand.map_fst _,ExclusionBand.map_snd _⟩

/-- Equation (31) evaluates the actual second marginal, rather than a candidate normalization. -/
theorem twoParameter_marginal_density (α β : ℝ) (hα : α ∈ Icc 0 (1/2)) (hβ : β ∈ Icc 0 (1/2)) (t : I) :
    let B := diagonalHoleBand α β hα hβ
    B.columnDensity t=(1-B.holeLength t)/(1-β) := ExclusionBand.columnDensity_eq _ _

/-- Proposition 3.5 and Equation (32), including both parameter endpoints. -/
theorem twoParameter_density (α β : ℝ) (hα : α ∈ Icc 0 (1/2)) (hβ : β ∈ Icc 0 (1/2)) :
    let B := diagonalHoleBand α β hα hβ
    (twoParameter α β hα hβ).toMeasure=
      (volume : Measure (Fin 2 → I)).withDensity (fun x => ENNReal.ofReal
        (if B.lower (x 0) ≤ (unitQuantile B.marginal (x 1) : ℝ) ∧
          (unitQuantile B.marginal (x 1) : ℝ) ≤ B.lower (x 0)+β then 0
        else 1/((1-β)*B.columnDensity (unitQuantile B.marginal (x 1))))) := by
  dsimp only
  change (diagonalHoleBand α β hα hβ).copula.toMeasure=_
  rw [ExclusionBand.copula_density]
  congr 1
  funext x
  rw [ExclusionBand.standardizedDensity_eq]
  rfl

/-- A zero-width hole gives independence along the entire bottom parameter edge. -/
theorem twoParameter_zero_width (α : ℝ) (hα : α ∈ Icc 0 (1/2)) :
    twoParameter α 0 hα (by norm_num)=Copula.independence 2 :=
  ExclusionBand.copula_eq_independence_of_width_zero _ rfl

/-- The upper corner is the same actual checkerboard as in Theorem 3.4. -/
theorem twoParameter_corner : twoParameter (1/2) (1/2) (by norm_num) (by norm_num)=antiCheckerboard := by
  apply Copula.ext
  change diagonalHoleCorner.copula.toMeasure=antiCheckerboard.toMeasure
  rw [diagonalHoleCorner_copula_density]
  symm
  apply Copula.toMeasure_eq_withDensity_of_cdf_integral _ medianOffDensity_cube_integrable
    (fun x => medianOffDensity_nonneg (x 0,x 1))
  intro x
  have he : x=![x 0,x 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [he]
  rw [medianOffDensity_cube_prefix]
  conv_rhs => rw [he]
  rw [antiCheckerboard_cdf]

/-- The corner's exact rank values; no numerical evaluation. -/
theorem twoParameter_corner_coefficients :
    (twoParameter (1/2) (1/2) (by norm_num) (by norm_num)).chatterjeeXi=1/2 ∧
    (twoParameter (1/2) (1/2) (by norm_num) (by norm_num)).spearmanFootrule= -1/2 := by
  rw [twoParameter_corner]
  exact ⟨antiCheckerboard_xi,antiCheckerboard_footrule⟩

/-- Equation (33) stays inside the proved closed parameter square for every finite mu. -/
theorem twoParameter_path_admissible (μ : ℝ) (hμ : 0 ≤ μ) :
    diagonalHoleAlpha μ ∈ Icc 0 (1/2) ∧ diagonalHoleBeta μ ∈ Icc 0 (1/2) :=
  diagonalHolePath_mem μ hμ

noncomputable def twoParameterPath (μ : ℝ) (hμ : 0 ≤ μ) : Copula 2 :=
  twoParameter (diagonalHoleAlpha μ) (diagonalHoleBeta μ)
    (twoParameter_path_admissible μ hμ).1 (twoParameter_path_admissible μ hμ).2

theorem twoParameter_path_zero : twoParameterPath 0 (by norm_num)=Copula.independence 2 := by
  unfold twoParameterPath
  have ha : diagonalHoleAlpha 0=0 := by norm_num [diagonalHoleAlpha]
  have hb : diagonalHoleBeta 0=0 := by norm_num [diagonalHoleBeta]
  simp only [ha,hb]
  exact twoParameter_zero_width _ _

end Papers.Rockel2026XiFootrule
