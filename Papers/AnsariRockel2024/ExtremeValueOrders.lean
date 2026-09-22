import Verification.ExtremeValuePickands
import Verification.MarshallOlkinOrder

/-! # Extreme-value CDF order and explicit monotone families -/

open ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Theorem 3.4(i)-(ii), with a canonical Pickands function recovered from max-stability.
The Schur equivalences for arbitrary extreme-value copulas are not asserted here. -/
theorem extremeValue_pickands_order (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    C.LowerOrthantLE D ↔ ∀ t : I, 0<t → t<1 → copulaPickands D t ≤ copulaPickands C t :=
  extremeValue_lowerOrthant_iff_pickands_interior C D hC hD

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

end Papers.AnsariRockel2024
