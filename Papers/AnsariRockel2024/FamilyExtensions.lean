import Papers.AnsariRockel2024.Dependence
import Copula.Dependence.FGMDensity
import Copula.Families.Nelsen7

/-! # Further FGM and Nelsen 7 table entries

Density TP2 is explicitly distinguished from TP2 of the CDF. The FGM
classification below concerns its displayed continuous density, together
with a genuine density witness in the nonnegative parameter range.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped unitInterval Topology

namespace Papers.AnsariRockel2024

theorem fgm_density (θ : ℝ) (hθ : |θ| ≤ 1) :
    (Copula.fgm θ hθ).toMeasure = (volume : Measure (Fin 2 → I)).withDensity
      (fun x => ENNReal.ofReal (1 + θ * (1 - 2 * (x 0 : ℝ)) * (1 - 2 * (x 1 : ℝ)))) :=
  Copula.toMeasure_fgm θ hθ

theorem fgm_density_tp2_iff (θ : ℝ) :
    IsTP2 (fun u v : I => 1 + θ * (1 - 2 * (u : ℝ)) * (1 - 2 * (v : ℝ))) ↔ 0 ≤ θ := by
  simpa only [Copula.isMTP2_fin_two_iff, Copula.fgmDensity,
    Matrix.cons_val_zero, Matrix.cons_val_one] using Copula.isMTP2_fgmDensity_iff θ

theorem fgm_has_tp2_density (θ : ℝ) (hθ : |θ| ≤ 1) (hpos : 0 ≤ θ) :
    (Copula.fgm θ hθ).HasMTP2Density := Copula.hasMTP2Density_fgm θ hθ hpos

theorem nelsen7_cdf (θ u v : I) :
    (Copula.nelsen7 θ).cdf ![u, v] =
      max 0 ((θ : ℝ) * (u : ℝ) * (v : ℝ) + (1 - (θ : ℝ)) * ((u : ℝ) + v - 1)) :=
  Copula.cdf_nelsen7 θ u v

theorem nelsen7_endpoints :
    Copula.nelsen7 0 = Copula.countermonotonic ∧ Copula.nelsen7 1 = Copula.independence 2 :=
  ⟨Copula.nelsen7_zero, Copula.nelsen7_one⟩

theorem nelsen7_cd (θ : I) : (Copula.nelsen7 θ).IsCD := Copula.isCD_nelsen7 θ

theorem nelsen7_lowerOrthant_iff (θ η : I) :
    (Copula.nelsen7 θ).LowerOrthantLE (Copula.nelsen7 η) ↔ θ ≤ η := by
  constructor
  · intro h
    have hh := h ![Copula.unitHalf, Copula.unitHalf]
    have he (t : I) : (Copula.nelsen7 t).cdf ![Copula.unitHalf, Copula.unitHalf] = (t : ℝ) / 4 := by
      rw [nelsen7_cdf]
      change max 0 ((t : ℝ) * (1 / 2) * (1 / 2) + (1 - t) * (1 / 2 + 1 / 2 - 1)) = _
      rw [show (t : ℝ) * (1 / 2) * (1 / 2) + (1 - t) * (1 / 2 + 1 / 2 - 1) = (t : ℝ) / 4 by ring,
        max_eq_right (div_nonneg t.property.1 (by norm_num : (0 : ℝ) ≤ 4))]
    rw [he, he] at hh
    change (θ : ℝ) ≤ η
    linarith
  · exact Copula.lowerOrthantLE_nelsen7

private theorem lower_tail_zero_of_le_independence (C : Copula 2)
    (h : C.LowerOrthantLE (Copula.independence 2)) : C.HasLowerTailDependence 0 := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    Copula.hasLowerTailDependence_independence
  · exact fun t => (C.lowerTailRatio_mem_Icc t).1
  · intro t
    exact div_le_div_of_nonneg_right (h ![t, t]) t.property.1

theorem nelsen7_tails (θ : I) :
    (Copula.nelsen7 θ).HasLowerTailDependence 0 ∧
    (Copula.nelsen7 θ).HasUpperTailDependence 0 := by
  have hlo : (Copula.nelsen7 θ).LowerOrthantLE (Copula.independence 2) := by
    simpa only [Copula.nelsen7_one] using Copula.lowerOrthantLE_nelsen7 (show θ ≤ (1 : I) from θ.property.2)
  constructor
  · exact lower_tail_zero_of_le_independence _ hlo
  · have hu := (Copula.upperOrthantLE_iff_lowerOrthantLE _ _).mpr hlo
    have hr := (Copula.upperOrthantLE_iff_reflect _ _).mp hu
    change (Copula.nelsen7 θ).survivalCopula.LowerOrthantLE (Copula.independence 2).survivalCopula at hr
    rw [Copula.isRadiallySymmetric_independence] at hr
    exact lower_tail_zero_of_le_independence _ hr

end Papers.AnsariRockel2024
