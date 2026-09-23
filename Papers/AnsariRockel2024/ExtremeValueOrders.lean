import Papers.AnsariRockel2024.GeneralOrders
import Verification.ExtremeValuePickands
import Verification.MarshallOlkinSingular
import Verification.MarshallOlkinRho
import Verification.MarshallOlkinXi
import Verification.MarshallOlkinTau

/-! # Extreme-value CDF order and explicit monotone families -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Theorem 3.4(i)-(ii), with a canonical Pickands function recovered from max-stability.
The Schur equivalences for arbitrary extreme-value copulas are not asserted here. -/
theorem extremeValue_pickands_order (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    C.LowerOrthantLE D ↔ ∀ t : I, 0<t → t<1 → copulaPickands D t ≤ copulaPickands C t :=
  extremeValue_lowerOrthant_iff_pickands_interior C D hC hD

private theorem lowerOrthantLE_transpose {C D : Copula 2}
    (h : C.LowerOrthantLE D) : C.transpose.LowerOrthantLE D.transpose := by
  intro z
  have hz : z = ![z 0, z 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hz]
  simpa only [Copula.cdf_transpose] using h ![z 1, z 0]

/-- The Schur part of Theorem 3.4 under the independently required CI premise. -/
theorem extremeValue_schur_iff_pickands_of_ci (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue)
    (hCI : C.IsCI) (hDI : D.IsCI) :
    C.SchurBothLE D ↔
      ∀ t : I, 0 < t → t < 1 → copulaPickands D t ≤ copulaPickands C t := by
  rw [← extremeValue_pickands_order C D hC hD]
  constructor
  · intro h
    exact (cis_schur_iff_orthant C D hCI.1 hDI.1).mp h.1
  · intro h
    constructor
    · exact (cis_schur_iff_orthant C D hCI.1 hDI.1).mpr h
    · exact (cis_schur_iff_orthant C.transpose D.transpose hCI.2 hDI.2).mpr
        (lowerOrthantLE_transpose h)

/-- The logarithmic-ray representation identifies the canonical function with
 the Pickands function in equation (3), including the axes. -/
theorem extremeValue_pickands_representation (C : Copula 2) (hC : C.IsExtremeValue)
    (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (hxy : 0<x+y) :
    C.cdf ![unitNegExp x hx,unitNegExp y hy] =
      Real.exp (-(x+y)*copulaPickands C ⟨y/(x+y),div_nonneg hy hxy.le,
        (div_le_one hxy).mpr (by linarith)⟩) :=
  extremeValue_exp_coordinates C hC x y hx hy hxy

/-- Table 1: the closed-square Marshall–Olkin formula. -/
theorem marshallOlkin_cdf (α β u v : I) :
    (Copula.marshallOlkin α β).cdf ![u,v] =
      min ((u:ℝ)^(1-(α:ℝ))*(v:ℝ)) ((u:ℝ)*(v:ℝ)^(1-(β:ℝ))) :=
  marshallOlkin_cdf_min α β u v

/-- Table 5: conditional increase in both directions, including singular parameters. -/
theorem marshallOlkin_ci (α β : I) : (Copula.marshallOlkin α β).IsCI :=
  marshallOlkin_isCI α β

/-- Table 5: coordinatewise parameter increase raises the lower orthant probabilities. -/
theorem marshallOlkin_orthant_mono {α β α' β' : I} (ha : α≤α') (hb : β≤β') :
    (Copula.marshallOlkin α β).LowerOrthantLE (Copula.marshallOlkin α' β') :=
  marshallOlkin_lowerOrthant_mono ha hb

/-- Table 5: both directional Schur comparisons. -/
theorem marshallOlkin_schur_mono {α β α' β' : I} (ha : α≤α') (hb : β≤β') :
    (Copula.marshallOlkin α β).SchurBothLE (Copula.marshallOlkin α' β') :=
  marshallOlkin_schurBoth_mono ha hb

theorem cuadrasAuge_ci (δ : I) : (Copula.cuadrasAuge δ).IsCI := marshallOlkin_isCI δ δ

theorem cuadrasAuge_orthant_mono {δ η : I} (h : δ≤η) :
    (Copula.cuadrasAuge δ).LowerOrthantLE (Copula.cuadrasAuge η) := marshallOlkin_lowerOrthant_mono h h

theorem cuadrasAuge_schur_mono {δ η : I} (h : δ≤η) :
    (Copula.cuadrasAuge δ).SchurBothLE (Copula.cuadrasAuge η) := marshallOlkin_schurBoth_mono h h

/-- Table 5: a genuine Lebesgue TP2 density exists exactly on the independence axes. -/
theorem marshallOlkin_density_tp2 (α β : I) :
    (Copula.marshallOlkin α β).HasMTP2Density ↔ α=0 ∨ β=0 := marshallOlkin_density_tp2_iff α β

/-- The singular component rules out any Lebesgue density off those axes. -/
theorem marshallOlkin_absolutelyContinuous (α β : I) :
    (Copula.marshallOlkin α β).toMeasure ≪ (MeasureTheory.volume : MeasureTheory.Measure (Fin 2 → I)) ↔ α=0 ∨ β=0 :=
  marshallOlkin_absolutelyContinuous_iff α β

/-- Every zero-weight axis is independence, not only the origin. -/
theorem marshallOlkin_independence_axes (α : I) :
    Copula.marshallOlkin 0 α=Copula.independence 2 ∧ Copula.marshallOlkin α 0=Copula.independence 2 :=
  ⟨marshallOlkin_zero_left α,marshallOlkin_zero_right α⟩

/-- Table 6: Spearman rho for the full two-parameter Marshall–Olkin family. -/
theorem marshallOlkin_rho (α β : I) :
    (Copula.marshallOlkin α β).spearmanRho =
      3 * (α : ℝ) * (β : ℝ) /
        (2 * (α : ℝ) + 2 * (β : ℝ) - (α : ℝ) * (β : ℝ)) :=
  Verification.marshallOlkin_spearmanRho α β

/-- Appendix A.5: the two-parameter conditional CDF, away from the shock curve. -/
theorem marshallOlkin_conditionalCDF (α β v : I) (ha : 0 < (α : ℝ)) :
    (fun u => (Copula.marshallOlkin α β).conditionalCDF u v) =ᵐ[volume]
      fun u => marshallOlkinConditional α β u v :=
  conditionalCDF_marshallOlkin α β v ha

/-- Table 6: Chatterjee xi for all Marshall–Olkin parameters, including singular laws. -/
theorem marshallOlkin_xi (α β : I) :
    (Copula.marshallOlkin α β).chatterjeeXi =
      2 * (α : ℝ) ^ 2 * (β : ℝ) /
        (3 * (α : ℝ) + (β : ℝ) - 2 * (α : ℝ) * (β : ℝ)) :=
  Verification.marshallOlkin_chatterjeeXi α β

/-- Table 6: Kendall tau for the full two-parameter Marshall–Olkin family. -/
theorem marshallOlkin_tau (α β : I) :
    (Copula.marshallOlkin α β).kendallTau =
      (α : ℝ) * (β : ℝ) /
        ((α : ℝ) + (β : ℝ) - (α : ℝ) * (β : ℝ)) :=
  Verification.marshallOlkin_kendallTau α β

end Papers.AnsariRockel2024
