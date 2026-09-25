import Papers.AnsariRockel2024.GeneralOrders
import Verification.ExtremeValuePickands
import Verification.ExtremeValueLog
import Verification.ExtremeValueConvexity
import Verification.ExtremeValueConditional
import Verification.PickandsConvexity
import Copula.ExtremeValue.Diagonal
import Verification.MarshallOlkinSingular
import Verification.MarshallOlkinRho
import Verification.MarshallOlkinXi
import Verification.MarshallOlkinTau

/-! # Extreme-value CDF order and explicit monotone families -/

open MeasureTheory ProbabilityTheory Verification
open scoped unitInterval

namespace Papers.AnsariRockel2024

/-- Theorem 3.4(i)-(ii), with a canonical Pickands function recovered from max-stability. -/
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

/-- Theorem 3.4(iv), in the copula conditional-CDF form, under CI. -/
theorem extremeValue_schur_first_iff_pickands_of_ci (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue)
    (hCI : C.IsCI) (hDI : D.IsCI) :
    C.SchurLE D ↔
      ∀ t : I, 0 < t → t < 1 → copulaPickands D t ≤ copulaPickands C t := by
  rw [← extremeValue_pickands_order C D hC hD]
  exact cis_schur_iff_orthant C D hCI.1 hDI.1

/-- Theorem 3.4(v), with the conditioning coordinates exchanged, under CI. -/
theorem extremeValue_schur_second_iff_pickands_of_ci (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue)
    (hCI : C.IsCI) (hDI : D.IsCI) :
    C.transpose.SchurLE D.transpose ↔
      ∀ t : I, 0 < t → t < 1 → copulaPickands D t ≤ copulaPickands C t := by
  rw [← extremeValue_pickands_order C D hC hD]
  constructor
  · intro h
    have ht := (cis_schur_iff_orthant C.transpose D.transpose hCI.2 hDI.2).mp h
    simpa using (lowerOrthantLE_transpose ht)
  · intro h
    exact (cis_schur_iff_orthant C.transpose D.transpose hCI.2 hDI.2).mpr
      (lowerOrthantLE_transpose h)

/-- Remark 3.5: Pickands order entails both classical concordance comparisons. -/
theorem extremeValue_pickands_concordance_mono (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue)
    (h : ∀ t : I, 0 < t → t < 1 → copulaPickands D t ≤ copulaPickands C t) :
    C.spearmanRho ≤ D.spearmanRho ∧ C.kendallTau ≤ D.kendallTau :=
  concordance_coefficients_mono C D ((extremeValue_pickands_order C D hC hD).mpr h)

/-- Remark 3.5: Pickands order entails both directional xi comparisons when CI is known. -/
theorem extremeValue_pickands_xi_mono_of_ci (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue)
    (hCI : C.IsCI) (hDI : D.IsCI)
    (h : ∀ t : I, 0 < t → t < 1 → copulaPickands D t ≤ copulaPickands C t) :
    C.chatterjeeXi ≤ D.chatterjeeXi ∧
      C.transpose.chatterjeeXi ≤ D.transpose.chatterjeeXi := by
  exact ⟨schur_xi_mono C D
    ((extremeValue_schur_first_iff_pickands_of_ci C D hC hD hCI hDI).mpr h),
    schur_xi_mono C.transpose D.transpose
      ((extremeValue_schur_second_iff_pickands_of_ci C D hC hD hCI hDI).mpr h)⟩

/-- Remark 3.5: both tail limits are ordered for max-stable copulas. -/
theorem extremeValue_pickands_tail_mono (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue)
    (h : ∀ t : I, 0 < t → t < 1 → copulaPickands D t ≤ copulaPickands C t) :
    (if C.extremalCoefficient = 1 then (1 : ℝ) else 0) ≤
      (if D.extremalCoefficient = 1 then (1 : ℝ) else 0) ∧
    2 - C.extremalCoefficient ≤ 2 - D.extremalCoefficient := by
  have ho := (extremeValue_pickands_order C D hC hD).mpr h
  exact ⟨ho.lowerTailDependence_le hC.hasPowerDiagonal.hasLowerTailDependence
    hD.hasPowerDiagonal.hasLowerTailDependence,
    ho.upperTailDependence_le hC.hasUpperTailDependence hD.hasUpperTailDependence⟩

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

theorem extremeValue_pickands_bounds (C : Copula 2) (hC : C.IsExtremeValue) (t : I) :
    max (1-(t:ℝ)) (t:ℝ)≤copulaPickands C t ∧ copulaPickands C t≤1 :=
  Verification.extremeValue_pickands_bounds C hC t

theorem extremeValue_log_homogeneous (C : Copula 2) (hC : C.IsExtremeValue)
    (x y t : ℝ) (hx : 0≤x) (hy : 0≤y) (ht : 0≤t) :
    extremeValueLog C (t*x) (t*y) (mul_nonneg ht hx) (mul_nonneg ht hy)=
      t*extremeValueLog C x y hx hy :=
  Verification.extremeValueLog_homogeneous C hC x y t hx hy ht

theorem extremeValue_log_submodular (C : Copula 2) (hC : C.IsExtremeValue)
    {x₁ x₂ y₁ y₂ : ℝ} (hx : 0≤x₁) (hy : 0≤y₁) (hxx : x₁≤x₂) (hyy : y₁≤y₂) :
    extremeValueLog C x₁ y₁ hx hy + extremeValueLog C x₂ y₂ (hx.trans hxx) (hy.trans hyy) ≤
      extremeValueLog C x₁ y₂ hx (hy.trans hyy) + extremeValueLog C x₂ y₁ (hx.trans hxx) hy :=
  Verification.extremeValueLog_submodular C hC hx hy hxx hyy

theorem extremeValue_log_increment_first (C : Copula 2) (hC : C.IsExtremeValue)
    {x₁ x₂ y : ℝ} (hx : 0≤x₁) (hy : 0≤y) (hxx : x₁≤x₂) :
    0≤extremeValueLog C x₂ y (hx.trans hxx) hy-extremeValueLog C x₁ y hx hy ∧
    extremeValueLog C x₂ y (hx.trans hxx) hy-extremeValueLog C x₁ y hx hy≤x₂-x₁ :=
  Verification.extremeValueLog_increment_first C hC hx hy hxx

theorem extremeValue_log_increment_second (C : Copula 2) (hC : C.IsExtremeValue)
    {x y₁ y₂ : ℝ} (hx : 0≤x) (hy : 0≤y₁) (hyy : y₁≤y₂) :
    0≤extremeValueLog C x y₂ hx (hy.trans hyy)-extremeValueLog C x y₁ hx hy ∧
    extremeValueLog C x y₂ hx (hy.trans hyy)-extremeValueLog C x y₁ hx hy≤y₂-y₁ :=
  Verification.extremeValueLog_increment_second C hC hx hy hyy

theorem extremeValue_log_section_convex (C : Copula 2) (hC : C.IsExtremeValue)
    (y : ℝ) (hy : 0≤y) : ConvexOn ℝ (Set.Ioi 0) (extremeValueLogSection C y hy) :=
  Verification.extremeValueLogSection_convex C hC y hy

/-- Every max-stable bivariate copula is conditionally increasing, without a density assumption. -/
theorem extremeValue_ci (C : Copula 2) (hC : C.IsExtremeValue) : C.IsCI :=
  Verification.extremeValue_isCI C hC

/-- Theorem 3.4(iii), without a separate CI hypothesis. -/
theorem extremeValue_schur_iff_pickands (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    C.SchurBothLE D ↔
      ∀ t : I, 0<t → t<1 → copulaPickands D t≤copulaPickands C t :=
  extremeValue_schur_iff_pickands_of_ci C D hC hD (extremeValue_ci C hC) (extremeValue_ci D hD)

/-- Theorem 3.4(iv), without a separate CI hypothesis. -/
theorem extremeValue_schur_first_iff_pickands (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    C.SchurLE D ↔
      ∀ t : I, 0<t → t<1 → copulaPickands D t≤copulaPickands C t :=
  extremeValue_schur_first_iff_pickands_of_ci C D hC hD (extremeValue_ci C hC) (extremeValue_ci D hD)

/-- Theorem 3.4(v), without a separate CI hypothesis. -/
theorem extremeValue_schur_second_iff_pickands (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue) :
    C.transpose.SchurLE D.transpose ↔
      ∀ t : I, 0<t → t<1 → copulaPickands D t≤copulaPickands C t :=
  extremeValue_schur_second_iff_pickands_of_ci C D hC hD (extremeValue_ci C hC) (extremeValue_ci D hD)

/-- Remark 3.5: both directional xi comparisons for arbitrary extreme-value copulas. -/
theorem extremeValue_pickands_xi_mono (C D : Copula 2)
    (hC : C.IsExtremeValue) (hD : D.IsExtremeValue)
    (h : ∀ t : I, 0<t → t<1 → copulaPickands D t≤copulaPickands C t) :
    C.chatterjeeXi≤D.chatterjeeXi ∧ C.transpose.chatterjeeXi≤D.transpose.chatterjeeXi :=
  extremeValue_pickands_xi_mono_of_ci C D hC hD (extremeValue_ci C hC) (extremeValue_ci D hD) h

/-- The real-coordinate extension agrees with the canonical Pickands function on its domain. -/
theorem extremeValue_pickands_real_coe (C : Copula 2) (hC : C.IsExtremeValue) (t : I) :
    copulaPickandsReal C t=copulaPickands C t := Verification.copulaPickandsReal_coe C hC t

/-- Section 2.1.2: convexity follows from the actual max-stable copula. -/
theorem extremeValue_pickands_convex (C : Copula 2) (hC : C.IsExtremeValue) :
    ConvexOn ℝ (Set.Icc 0 1) (copulaPickandsReal C) := Verification.copulaPickandsReal_convex C hC

end Papers.AnsariRockel2024
