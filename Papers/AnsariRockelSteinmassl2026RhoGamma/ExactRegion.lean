import Copula.Rank.Region.RhoGamma.Exact
import Papers.AnsariRockelSteinmassl2026RhoGamma.Moments

/-! # The full sharp rho-gamma region

Boundary coordinates are explicit arithmetic expressions from the package.
Both reflected boundaries are attained, as is every point between them.
-/

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace Papers.AnsariRockelSteinmassl2026RhoGamma

open Copula.RankRegion

abbrev BoundaryParameter := RhoGamma.UpperParameter

noncomputable def upperRho (g : ℝ) : ℝ :=
  if h : g ∈ Set.Icc (-1) 1 then (RhoGamma.upperParameter_exists h).choose.rho else 0

theorem boundary_coefficients (a : BoundaryParameter) :
    a.copula.giniGamma = a.gamma ∧ a.copula.spearmanRho = a.rho :=
  ⟨a.gamma_coefficient, a.rho_coefficient⟩

theorem upperRho_parameter (a : BoundaryParameter) : upperRho a.gamma = a.rho := by
  have hg : a.gamma ∈ Set.Icc (-1) 1 := a.gamma_coefficient ▸ a.copula.giniGamma_mem_Icc
  rw [upperRho, dite_eq_left hg]
  exact RhoGamma.upperParameter_rho_unique _ a (RhoGamma.upperParameter_exists hg).choose_spec

theorem sharp_upper_bound (C : Copula 2) : C.spearmanRho ≤ upperRho C.giniGamma := by
  obtain ⟨a, ha⟩ := RhoGamma.upperParameter_exists C.giniGamma_mem_Icc
  rw [← ha, upperRho_parameter]
  exact a.maximizes C ha.symm

theorem sharp_lower_bound (C : Copula 2) : -upperRho (-C.giniGamma) ≤ C.spearmanRho := by
  have h := sharp_upper_bound (C.reflect {1})
  rw [Copula.spearmanRho_reflect_second, Copula.giniGamma_reflect_second] at h
  linarith

theorem upper_boundary_attained {g : ℝ} (hg : g ∈ Set.Icc (-1) 1) :
    ∃ C : Copula 2, C.giniGamma = g ∧ C.spearmanRho = upperRho g := by
  obtain ⟨a, ha⟩ := RhoGamma.upperParameter_exists hg
  exact ⟨a.copula, a.gamma_coefficient.trans ha,
    a.rho_coefficient.trans (ha ▸ upperRho_parameter a).symm⟩

theorem lower_boundary_attained {g : ℝ} (hg : g ∈ Set.Icc (-1) 1) :
    ∃ C : Copula 2, C.giniGamma = g ∧ C.spearmanRho = -upperRho (-g) := by
  obtain ⟨C, hC, hr⟩ := upper_boundary_attained
    (show -g ∈ Set.Icc (-1 : ℝ) 1 by constructor <;> linarith [hg.1, hg.2])
  exact ⟨C.reflect {1}, by rw [Copula.giniGamma_reflect_second, hC, neg_neg],
    by rw [Copula.spearmanRho_reflect_second, hr]⟩

/-- Theorem 1.1, equation (6), with no supplied optimizer hypothesis. -/
theorem exact_region (r g : ℝ) :
    (r, g) ∈ region ↔ g ∈ Set.Icc (-1) 1 ∧ -upperRho (-g) ≤ r ∧ r ≤ upperRho g := by
  constructor
  · rintro ⟨C, hC⟩
    cases hC
    exact ⟨C.giniGamma_mem_Icc, sharp_lower_bound C, sharp_upper_bound C⟩
  · rintro ⟨hg, hl, hu⟩
    obtain ⟨L, hLg, hLr⟩ := lower_boundary_attained hg
    obtain ⟨U, hUg, hUr⟩ := upper_boundary_attained hg
    obtain ⟨C, hCg, hCr⟩ := fixed_gamma_intermediate L U hLg hUg (hLr ▸ hl) (hUr ▸ hu)
    exact ⟨C, Prod.ext hCr hCg⟩

theorem boundary_value_unique (a b : BoundaryParameter) (h : a.gamma = b.gamma) :
    a.rho = b.rho := RhoGamma.upperParameter_rho_unique a b h

/-- Explicit constructed certificates cover every auxiliary branch. -/
theorem glued_dual_feasible (A : RhoGamma.AuxiliaryCertificate) (u v : I) :
    min (u : ℝ) v * |max (u : ℝ) v - A.t| ≤ A.dual u + A.dual v := A.dual_feasible u v

/-- Theorem 4.2: global support bound for each concrete glued optimizer. -/
theorem sharp_supporting_bound (A : RhoGamma.AuxiliaryCertificate) (C : Copula 2) :
    C.spearmanRho - 3 / 2 * A.t * C.giniGamma ≤
      A.copula.spearmanRho - 3 / 2 * A.t * A.copula.giniGamma := A.supporting_bound C

end Papers.AnsariRockelSteinmassl2026RhoGamma
